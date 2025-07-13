#define ZYDIS_STATIC_DEFINE

#include <Windows.h>
#include <Psapi.h>

#include <vector>
#include <string>
#include <filesystem>
#include <unordered_map>
#include <thread>
#include <mutex>
#include <iostream>
#include <queue>

#include <Zydis/Decoder.h>
#include <Zydis/Utils.h>

namespace g
{
    uintptr_t base;

    uintptr_t text_start, text_end;
    uintptr_t rdata_start, rdata_end;

    ZydisDecoder decoder;
    ZydisDecodedInstruction instruction;
    ZydisDecodedOperand operands[ZYDIS_MAX_OPERAND_COUNT];
}

#define rebase(x) x - g::base

std::vector<std::uintptr_t> sig_scan(const std::uintptr_t start_address, const std::uintptr_t end_address, 
                                     const std::uint8_t* pattern, const std::string& mask)
{
    std::vector<std::uintptr_t> result;
    for (auto addr = (std::uint8_t*)(start_address); addr < (std::uint8_t*)(end_address - mask.length()); addr++)
    {
        for (unsigned long long i = 0ull; i < mask.length(); i++)
        {
            if (mask[i] != '?' and *(addr + i) != static_cast<std::uint8_t>(pattern[i]))
            {
                goto out_of_scope;
            }
        }
        result.push_back(reinterpret_cast<std::uintptr_t>(addr));
out_of_scope:
        continue;
    }
    return result;
}

std::vector<std::int32_t> init_vpn_start_offsets() {
    std::vector<std::int32_t> page_first_instructions{};

    page_first_instructions.insert(page_first_instructions.begin(), ((g::text_end - g::text_start) / 0x1000) + 1, 0);

    int i = 1;
    for (auto addr = g::text_start; addr < g::text_end;) {
        if (!std::memcmp(reinterpret_cast<void*>(addr), "\x90\x90\x90\x90\x90\x90\x90\x90", 8))
        {
            addr += 0x1000;
        }

        if (const auto status =
            ZydisDecoderDecodeFull(
                &g::decoder,
                reinterpret_cast<std::uint8_t*>(addr),
                0x10,
                &g::instruction,
                g::operands
            )
            ; ZYAN_SUCCESS(status))
        {
            if ((addr % 0x1000 >= 0xFF0) && (addr % 0x1000) + g::instruction.length >= 0x1000)
            {
                page_first_instructions[i] = addr % 0x1000 + g::instruction.length - 0x1000;
                i++;
            }

            addr += g::instruction.length;
        }
        else
        {
            addr += max(0x10 - addr % 0x10, 1ull);
        }
    }

    page_first_instructions.push_back(0);

    return page_first_instructions;
}

std::vector<std::uintptr_t> ref_scan(std::uintptr_t address, bool stop_first)
{
    static std::vector<std::int32_t> page_first_instructions = init_vpn_start_offsets();

    std::vector<std::thread> analysis_threads;

    std::mutex ret_mutex;
    std::vector<std::uintptr_t> result;

    auto scan_page = [address, &ret_mutex, &result](const std::uintptr_t start_address, const std::uintptr_t size)
    {
        ZydisDecoder decoder2;
        ZydisDecodedInstruction instruction2;
        ZydisDecodedOperand operands2[ZYDIS_MAX_OPERAND_COUNT];
        ZydisDecoderInit(&decoder2, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);
        std::vector<std::uintptr_t> local_result;
        for (auto addr = start_address; addr < start_address + size;)
        {
            if (const auto status =
                ZydisDecoderDecodeFull(
                    &decoder2,
                    reinterpret_cast<std::uint8_t*>(addr),
                    0x10,
                    &instruction2,
                    operands2
                )
                ; ZYAN_SUCCESS(status))
            {
                switch (instruction2.mnemonic)
                {
                    case ZYDIS_MNEMONIC_MOV:
                        if (operands2[0].type == ZYDIS_OPERAND_TYPE_REGISTER) {
                            if (operands2[1].type == ZYDIS_OPERAND_TYPE_MEMORY && addr + operands2[1].mem.disp.value
                                +
                                instruction2.length == address)
                                local_result.push_back(addr + operands2[1].mem.disp.value + instruction2.length);
                        }
                        break;
                    case ZYDIS_MNEMONIC_LEA:
                        if (operands2[0].type == ZYDIS_OPERAND_TYPE_REGISTER)
                        {
                            if (operands2[1].type == ZYDIS_OPERAND_TYPE_MEMORY && addr + operands2[1].mem.disp.value +
                                instruction2.length == address)
                            {
                                local_result.push_back(addr);
                            }
                        }
                    default: break;
                }

                addr += instruction2.length;
            }
            else
            {
                addr += 0x10 - addr % 0x10;
            }
        }


        if (!local_result.empty())
        {
            ret_mutex.lock();
            for (const auto& c : local_result)
            {
                result.push_back(c);
            }

            ret_mutex.unlock();
        }
    };

    int i = 0;
    for (auto addr = g::text_start; addr < g::text_end; addr += 0x1000)
    {
        if (!std::memcmp(reinterpret_cast<void*>(addr), "\x90\x90\x90\x90\x90\x90\x90\x90", 8))
        {
            continue;
        }

        std::thread analyze_page(scan_page, addr + page_first_instructions[i], (g::text_end - addr <= 0x1000) ? g::text_end - addr : 0x1000);
        analysis_threads.push_back(std::move(analyze_page));

        i++;
    }

    for (auto& thread : analysis_threads)
    {
        thread.join();
    }

    return result;
}

std::vector<std::uintptr_t> string_xref_scan(const std::string& str, int nresult, bool rdata_only,
                                             bool scan_code, bool stop_first) {
    std::vector<std::uintptr_t> result;
    std::vector<std::uint8_t> str_pat_1(1, 0x0);
    str_pat_1.insert(str_pat_1.end(), str.begin(), str.end());
    str_pat_1.push_back(0);
    const auto& str_locs = sig_scan(rdata_only ? g::rdata_start : g::text_start, g::rdata_end, str_pat_1.data(),
                                    std::string(str_pat_1.size(), 'x'));
    if (str_locs.empty())
    {
        return std::printf("No results for %s\r\n", str.c_str()), result;
    }

    if (str_locs.size() - 1 < nresult)
    {
        return std::printf("Not enough results for %d, found %llu\r\n", nresult, str_locs.size() - 1), result;
    }

    const auto str_addr = str_locs[nresult] + 1;

    if (scan_code)
    {
        result = ref_scan(str_addr, stop_first);
    }

    uint8_t pattern[] =
    {
        static_cast<unsigned char>(str_addr & 0xFF),
        static_cast<unsigned char>(str_addr >> 8 & 0xFF),
        static_cast<unsigned char>(str_addr >> 16 & 0xFF),
        static_cast<unsigned char>(str_addr >> 24 & 0xFF),
        static_cast<unsigned char>(str_addr >> 32 & 0xFF),
        static_cast<unsigned char>(str_addr >> 40 & 0xFF),
        static_cast<unsigned char>(str_addr >> 48 & 0xFF),
        static_cast<unsigned char>(str_addr >> 56 & 0xFF)
    };

    const auto& res_2 = sig_scan(g::rdata_start, g::rdata_end, pattern, "xxxxxxxx");
    result.insert(result.end(), res_2.begin(), res_2.end());

    return result;
}

std::uintptr_t find_next(const std::uintptr_t address, const ZydisMnemonic_ mnemonic, const int idx)
{
    std::uintptr_t current_address = address;

    int counter = 0;
    while (ZYAN_SUCCESS(ZydisDecoderDecodeFull(
        &g::decoder,
        reinterpret_cast<std::uint8_t*>(current_address),
        0x10,
        &g::instruction,
        g::operands)))
    {
        if (g::instruction.mnemonic == mnemonic && counter++ == idx)
        {
            return current_address;
        }

        current_address += g::instruction.length;
    }

    return 0;
}

std::uintptr_t resolve_data_ref(std::uintptr_t addr, const int op_idx)
{
    ZyanU64 absolute;
    const auto op = g::operands[op_idx];
    ZydisCalcAbsoluteAddress(&g::instruction, &op, addr, &absolute);

    return absolute;
}

void change_protection(uintptr_t base, size_t size)
{
    for (uintptr_t address = base; address < base + size;)
    {
        MEMORY_BASIC_INFORMATION mbi;
        VirtualQuery(PVOID(address), &mbi, sizeof(mbi));
        VirtualProtect(PVOID(address), mbi.RegionSize, PAGE_EXECUTE_READWRITE, &mbi.Protect);
        address += mbi.RegionSize;
    }
}

int main(int argc, char* argv[])
{
    if (argc != 2)
    {
        return printf("file arg missing, usage: dumper.exe <name.ext>"), 1;
    }

    if (!std::filesystem::exists(argv[1]))
    {
        return printf("file doesn't exist"), 2;
    }

    const HMODULE module = LoadLibraryA(argv[1]);

    MODULEINFO mod_info;
    if (!K32GetModuleInformation(GetCurrentProcess(), module, &mod_info, sizeof(mod_info)))
    {
        return std::printf("failed to get module info: %02X", GetLastError()), 3;
    }

    g::base = uintptr_t(mod_info.lpBaseOfDll);
    size_t size = size_t(mod_info.SizeOfImage);

    change_protection(g::base, size);

    const PIMAGE_DOS_HEADER dos_header = PIMAGE_DOS_HEADER(g::base);
    const PIMAGE_NT_HEADERS nt_headers = PIMAGE_NT_HEADERS(g::base + dos_header->e_lfanew);
    const PIMAGE_SECTION_HEADER sections = IMAGE_FIRST_SECTION(nt_headers);

    for (int i = 0; i < nt_headers->FileHeader.NumberOfSections; ++i)
    {
        auto section = sections[i];

        if (memcmp(section.Name, ".text", 5) == 0)
        {
            g::text_start = g::base + section.VirtualAddress;
            g::text_end = g::text_start + section.SizeOfRawData;
        }
        else if (memcmp(section.Name, ".rdata", 6) == 0)
        {
            g::rdata_start = g::base + section.VirtualAddress;
            g::rdata_end = g::rdata_start + section.SizeOfRawData;
        }
    }

    ZydisDecoderInit(&g::decoder, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_STACK_WIDTH_64);

    // signature scanning logic, doesn't use the disassembler

    //48 8B C4 48 89 50 ? 4C 89 40 ? 4C 89 48 ? 53 57 48 83 EC 78
    uint8_t print_pattern[] =
    {
        0x48, 0x8B, 0xC4, 0x48, 0x89, 0x50, 0x00, 0x4C, 0x89, 0x40, 0x00,
        0x4C, 0x89, 0x48, 0x00, 0x53, 0x57, 0x48, 0x83, 0xEC, 0x78
    };
    std::string print_mask("xxxxxx?xxx?xxx?xxxxxx");

    const std::vector<uintptr_t>& sigs = sig_scan(g::text_start, g::text_end, print_pattern, print_mask);
    if (sigs.size() > 0)
    {
        // rebase will give you a usable offset for your cheat
        printf("print -> 0x%llx\n", rebase(sigs[0]));
    }
    else
    {
        printf("no results found\n");
    }

    const std::vector<uintptr_t> xrefs = string_xref_scan("Script Start", 0, true, true, true);
    if (xrefs.size() > 0)
    {
        const auto script_start_ref = xrefs[0] /*cross reference to the "Script Start" string*/ - 0x3D /*offset + leeway to give room for potential changes to code*/;

        // we find the next instruction of a specific type (mnemonic) from an address + index. 0 gets the first, 1 the second, etc
        auto decrypt_global_state_call = find_next(script_start_ref, ZYDIS_MNEMONIC_CALL, 1);
        // resolve_data_ref is for getting the address referenced in one of these instructions
        uintptr_t decrypt_gs = rebase(resolve_data_ref(decrypt_global_state_call, 0));

        printf("decrypt gs -> 0x%llx\n", decrypt_gs);
    }
    else
    {
        printf("no xrefs found\n");
    }

    return std::getchar();
}
