#include "prx/libSceAgcDriver/Execution/include/VulkanDevice.hpp"
#include "prx/libSceAgcDriver/Execution/include/Driver/Shaders/ShaderRegistry.hpp"
#include "prx/libSceAgcDriver/Graphics/include/Draw.hpp"
#include "Optimization/ResourceProgram.hpp"
#include "Recompiler.hpp"
#include "VulkanTestDevice.hpp"
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <iostream>
#include <mutex>
#include <span>
#include <string>
#include <vector>

namespace {

using AgcDriver::Graphics::Require;
using ShaderRecompiler::ShaderStage;

constexpr std::uint32_t MaxThreads = 64;
constexpr std::uint32_t Inputs = 4;
constexpr std::uint32_t Results = 4;
alignas(256) std::array<std::uint32_t, MaxThreads * Inputs> Input{};
alignas(256) std::array<std::uint32_t, MaxThreads * Results> Output{};

alignas(256) constexpr std::array<std::uint32_t, 10> Caller{0x34020084u, 0xe0381000u, 0x80000401u, 0xbf8c3f70u, 0xbe8e0308u, 0xbe8f0309u, 0xbe8e210eu, 0xe0781000u, 0x80010401u, 0xbf810000u};
alignas(256) constexpr std::array<std::uint32_t, 13> ChainedCaller{0x34020084u, 0xe0381000u, 0x80000401u, 0xbf8c3f70u, 0xbe8e0308u, 0xbe8f0309u, 0xbe8e210eu, 0xbe8e030au, 0xbe8f030bu, 0xbe8e210eu, 0xe0781000u, 0x80010401u, 0xbf810000u};
alignas(256) std::array<std::uint32_t, 8> Arithmetic{0x4a0808ffu, 0x13579bdfu, 0x3a0a0affu, 0xa5a5a5a5u, 0x4a0c0f06u, 0x3a0e0effu, 0x5a5a5a5au, 0xbe80200eu};
alignas(256) constexpr std::array<std::uint32_t, 3> Mask{0x3a0808ffu, 0x0f0f0f0fu, 0xbe80200eu};

constexpr std::array<std::uint32_t, 8> Selectors{0u, 1u, 2u, 3u, 4u, 7u, 0x80000000u, 0xffffffffu};

struct Variant {
    const char* name;
    std::uint64_t callee;
    std::function<std::uint32_t(std::uint32_t, std::uint32_t)> expected;
    std::uint64_t secondCallee = 0;
};

std::array<std::uint32_t, 4> BufferDescriptor(const void* data, std::uint32_t bytes) {
    const auto address = reinterpret_cast<std::uintptr_t>(data);
    return {static_cast<std::uint32_t>(address), static_cast<std::uint32_t>((address >> 32u) & 0xffffu), bytes, 0x31016facu};
}

std::string Hex(std::uint32_t value) {
    char text[16];
    std::snprintf(text, sizeof(text), "0x%08x", value);
    return text;
}

std::uint32_t ArithmeticExpected(std::uint32_t lane, std::uint32_t result, std::uint32_t addend) {
    switch (result) {
        case 0: return Input[lane * Inputs] + addend;
        case 1: return Input[lane * Inputs + 1u] ^ 0xa5a5a5a5u;
        case 2: return Input[lane * Inputs + 2u] + Input[lane * Inputs + 3u];
        default: return Input[lane * Inputs + 3u] ^ 0x5a5a5a5au;
    }
}

std::uint32_t MaskExpected(std::uint32_t lane, std::uint32_t result) {
    return result == 0 ? Input[lane * Inputs] ^ 0x0f0f0f0fu : Input[lane * Inputs + result];
}

std::vector<std::uint32_t> UserData(std::uint64_t callee, std::uint64_t secondCallee = 0) {
    std::vector<std::uint32_t> userData(12, 0u);
    const auto input = BufferDescriptor(Input.data(), static_cast<std::uint32_t>(Input.size() * 4u));
    const auto output = BufferDescriptor(Output.data(), static_cast<std::uint32_t>(Output.size() * 4u));
    std::copy(input.begin(), input.end(), userData.begin());
    std::copy(output.begin(), output.end(), userData.begin() + 4);
    userData[8] = static_cast<std::uint32_t>(callee);
    userData[9] = static_cast<std::uint32_t>(callee >> 32u);
    userData[10] = static_cast<std::uint32_t>(secondCallee);
    userData[11] = static_cast<std::uint32_t>(secondCallee >> 32u);
    return userData;
}

ShaderRecompiler::RecompileRequest Request(const AgcDriver::DriverDetail::ShaderSnapshot& snapshot, std::span<const std::uint32_t> userData, std::uint32_t waveSize, const ShaderRecompiler::SpirvTarget& target, std::span<const ShaderRecompiler::MemoryRegion> memory) {
    const ShaderRecompiler::ShaderComputeStageInfo compute{{waveSize, 1, 1}, 0u, {false, false, false}, false, 1};
    return ShaderRecompiler::RecompileRequest{
        {ShaderStage::Compute, snapshot.codeAddress, snapshot.code, 0, {}},
        {waveSize, 0, userData, compute, std::nullopt, std::nullopt, memory},
        target,
        {0, 0, 0, 128}
    };
}

void Run(AgcDriver::VulkanDevice& device, AgcDriver::DriverDetail::ShaderSnapshot& snapshot, const Variant& variant, std::uint32_t waveSize, const ShaderRecompiler::SpirvTarget& target) {
    for (std::uint32_t tid = 0; tid < MaxThreads; ++tid) {
        Input[tid * Inputs] = Selectors[tid % Selectors.size()];
        Input[tid * Inputs + 1u] = 0x9e3779b9u * (tid + 1u);
        Input[tid * Inputs + 2u] = 0xffffffffu - tid;
        Input[tid * Inputs + 3u] = 17u * tid + 1u;
    }
    Output.fill(0xdeadbeefu);
    const auto userData = UserData(variant.callee, variant.secondCallee);
    const std::array<ShaderRecompiler::MemoryRegion, 1> memory{{{snapshot.codeAddress, std::as_bytes(std::span(snapshot.code))}}};
    const auto request = Request(snapshot, userData, waveSize, target, memory);
    const auto invocation = AgcDriver::DriverDetail::InvocationFor(snapshot, 0, request);
    ShaderRecompiler::SrtRuntime runtime{};
    runtime.userData = userData;
    const auto capture = invocation.Capture(runtime);
    const auto result = invocation.Materialize(*capture);
    device.Dispatch(*result, 1, 1, 1, {}, snapshot.codeAddress);
    device.WaitIdle();
    for (std::uint32_t tid = 0; tid < waveSize; ++tid) {
        for (std::uint32_t index = 0; index < Results; ++index) {
            const auto actual = Output[tid * Results + index];
            const auto expected = variant.expected(tid, index);
            Require(actual == expected, std::string(variant.name) + " wave" + std::to_string(waveSize) + ": lane " + std::to_string(tid) + " result " + std::to_string(index) + " is " + Hex(actual) + ", expected " + Hex(expected));
        }
    }
    for (std::uint32_t index = waveSize * Results; index < Output.size(); ++index) {
        Require(Output[index] == 0xdeadbeefu, std::string(variant.name) + ": inactive lane wrote output");
    }
}

std::size_t Entries(const AgcDriver::DriverDetail::ShaderSnapshot& snapshot) {
    std::lock_guard lock(snapshot.prepared->mutex);
    return snapshot.prepared->entries.size();
}

}

int main() {
    try {
        const auto device = OpenVulkanTestDevice();
        if (!device) return VulkanTestSkipped;
        const auto wave64Target = device->Target();
        const auto wave32Target = device->ComputeTarget(32);
        AgcDriver::DriverDetail::ShaderSnapshot snapshot{reinterpret_cast<std::uintptr_t>(Caller.data()), 0, 0, {Caller.begin(), Caller.end()}, {}};
        const auto arithmetic = reinterpret_cast<std::uintptr_t>(Arithmetic.data());
        const Variant first{"arithmetic callee", arithmetic, [](std::uint32_t lane, std::uint32_t result) { return ArithmeticExpected(lane, result, 0x13579bdfu); }};
        Run(*device, snapshot, first, 32, wave32Target);
        Require(Entries(snapshot) == 1, "the first dispatch did not prepare exactly one artifact");
        Run(*device, snapshot, first, 64, wave64Target);
        const auto afterWave64 = Entries(snapshot);
        Run(*device, snapshot, first, 32, wave32Target);
        Require(Entries(snapshot) == afterWave64, "an unchanged callee was prepared again");

        Arithmetic[1] = 0x2468ace0u;
        const Variant changed{"changed callee bytes", arithmetic, [](std::uint32_t lane, std::uint32_t result) { return ArithmeticExpected(lane, result, 0x2468ace0u); }};
        Run(*device, snapshot, changed, 32, wave32Target);
        Require(Entries(snapshot) == afterWave64 + 1, "a changed callee did not prepare a new artifact");

        const Variant mask{"callee at another address", reinterpret_cast<std::uintptr_t>(Mask.data()), MaskExpected};
        Run(*device, snapshot, mask, 32, wave32Target);
        Require(Entries(snapshot) == afterWave64 + 2, "a callee at another address did not prepare a new artifact");
        Run(*device, snapshot, changed, 32, wave32Target);
        Require(Entries(snapshot) == afterWave64 + 2, "a callee seen before was prepared again");

        AgcDriver::DriverDetail::ShaderSnapshot chained{reinterpret_cast<std::uintptr_t>(ChainedCaller.data()), 0, 0, {ChainedCaller.begin(), ChainedCaller.end()}, {}};
        const Variant twoCalls{"two calls through one link pair", arithmetic, [](std::uint32_t lane, std::uint32_t result) { return result == 0 ? ArithmeticExpected(lane, result, 0x2468ace0u) ^ 0x0f0f0f0fu : ArithmeticExpected(lane, result, 0x2468ace0u); }, reinterpret_cast<std::uintptr_t>(Mask.data())};
        Run(*device, chained, twoCalls, 32, wave32Target);
        Run(*device, chained, twoCalls, 64, wave64Target);
        Require(Entries(chained) == 2, "the chained caller did not prepare one artifact per wave size");

        const auto userData = UserData(0);
        const std::array<ShaderRecompiler::MemoryRegion, 1> memory{{{snapshot.codeAddress, std::as_bytes(std::span(snapshot.code))}}};
        const auto nullRequest = Request(snapshot, userData, 32, wave32Target, memory);
        try {
            static_cast<void>(AgcDriver::DriverDetail::InvocationFor(snapshot, 0, nullRequest));
            throw std::runtime_error("a null call target was accepted");
        } catch (const std::runtime_error& error) {
            Require(std::string(error.what()).find("null or misaligned") != std::string::npos, error.what());
        }
        std::printf("user-data call execution passed: %zu prepared artifacts\n", Entries(snapshot));
        return 0;
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
