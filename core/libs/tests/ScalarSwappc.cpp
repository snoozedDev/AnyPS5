#include "ControlFlow/GraphBuilder.hpp"
#include "IntermediateRepresentation/IrProgram.hpp"
#include "RdnaDecoder/RdnaInstructionDecoder.hpp"
#include "RdnaDecoder/RdnaScalarOpDecoder.hpp"
#include "Translation/TranslationContext.hpp"
#include <array>
#include <vector>
#include <cstdio>
#include <stdexcept>
#include <string>

using namespace ShaderRecompiler;
static void Require(bool value) { if (!value) throw std::runtime_error("scalar swappc regression"); }

template <typename Fn>
static void ExpectThrow(const char* needle, Fn fn) {
    try {
        fn();
    } catch (const std::exception& error) {
        if (std::string(error.what()).find(needle) == std::string::npos) {
            throw std::runtime_error(std::string("wrong error for \"") + needle + "\": " + error.what());
        }
        return;
    }
    throw std::runtime_error(std::string("expected throw containing \"") + needle + "\"");
}

static RdnaInstruction Sop1(std::uint32_t pc, std::uint32_t sdst, std::uint32_t opcode, std::uint32_t ssrc0) {
    const std::array<std::uint32_t, 2> words{0x80000000u | (0x7du << 23u) | (sdst << 16u) | (opcode << 8u) | ssrc0, 0u};
    return DecodeRdnaSop1(pc, words, 0u);
}

static RdnaInstruction Sop2Literal(std::uint32_t pc, std::uint32_t sdst, std::uint32_t opcode, std::uint32_t ssrc0, std::uint32_t literal) {
    const std::array<std::uint32_t, 2> words{0x80000000u | (opcode << 23u) | (sdst << 16u) | (0xffu << 8u) | ssrc0, literal};
    return DecodeRdnaSop2(pc, words, 0u);
}

static RdnaInstruction Sopp(std::uint32_t pc, std::uint32_t opcode, std::uint32_t simm16 = 0u) {
    const std::array<std::uint32_t, 1> words{0x80000000u | (0x7fu << 23u) | (opcode << 16u) | (simm16 & 0xffffu)};
    return DecodeRdnaSopp(pc, words, 0u);
}

static RdnaInstruction Sopk(std::uint32_t pc, std::uint32_t opcode, std::uint32_t sdst, std::uint32_t simm16) {
    const std::array<std::uint32_t, 1> words{0x80000000u | ((0x60u + opcode) << 23u) | (sdst << 16u) | (simm16 & 0xffffu)};
    return DecodeRdnaSopk(pc, words, 0u);
}

static RdnaProgram Program(std::initializer_list<RdnaInstruction> instructions) {
    RdnaProgram program;
    program.instructions.assign(instructions);
    return program;
}

static ControlFlowGraph Build(const RdnaProgram& program, const SwappcInfo* swappc = nullptr) {
    return GraphBuilder{}.Build(program, swappc);
}

static void CheckDecodeIdentity() {
    const std::array<std::uint32_t, 2> words{0x80000000u | (0x7du << 23u) | (8u << 16u) | (0x21u << 8u) | 4u, 0u};
    const RdnaInstruction instruction = DecodeRdnaSop1(0x24u, words, 0u);
    Require(instruction.op == RdnaOpcode::SSwappcB64);
    Require(instruction.family == RdnaInstructionFamily::SOP1);
    Require(instruction.programCounter == 0x24u);
    Require(instruction.dataDwordCount == 2u);
    Require(instruction.sourceCount == 1u);
    Require(instruction.source0.kind == RdnaOperandKind::ScalarRegister && instruction.source0.reg == 4u);
    Require(instruction.destination.kind == RdnaOperandKind::ScalarRegister && instruction.destination.reg == 8u);

    const std::array<std::uint32_t, 2> pcWords{0x80000000u | (0x7du << 23u) | (125u << 16u) | (0x21u << 8u) | 4u, 0u};
    Require(DecodeRdnaSop1(0u, pcWords, 0u).op == RdnaOpcode::SSetpcB64);


    const RdnaInstruction add = Sop2Literal(0x4u, 4u, 0x00u, 4u, 0x18u);
    Require(add.op == RdnaOpcode::SAddU32);
    Require(add.wordCount == 2u);
}

static std::string TranslateDump(const RdnaInstruction& instruction) {
    IrProgram program;
    auto& block = program.CreateBlock();
    program.SetEntryBlock(block);
    program.BlockOrder() = {&block};
    program.Metadata().blockInfo.resize(1);
    TranslationContext context(program, block, 256);
    context.TranslateInstruction(instruction);
    return ProgramToString(program);
}

static void CheckLinkModelsNextInstructionAddress() {
    const std::array<std::uint32_t, 2> getpcWords{0x80000000u | (0x7du << 23u) | (2u << 16u) | (0x1fu << 8u), 0u};
    const std::array<std::uint32_t, 2> swappcWords{0x80000000u | (0x7du << 23u) | (2u << 16u) | (0x21u << 8u) | 4u, 0u};
    const RdnaInstruction getpc = DecodeRdnaSop1(0x10u, getpcWords, 0u);
    const RdnaInstruction swappc = DecodeRdnaSop1(0x10u, swappcWords, 0u);
    Require(!TranslateDump(getpc).empty());
    Require(TranslateDump(getpc) == TranslateDump(swappc));
}

static void CheckStaticCallRegion() {
    const auto program = Program({
        Sop1(0x00u, 4u, 0x1fu, 0u),
        Sop2Literal(0x04u, 4u, 0x00u, 4u, 0x18u),
        Sop2Literal(0x0cu, 5u, 0x04u, 5u, 0u),
        Sop1(0x14u, 8u, 0x21u, 4u),
        Sopp(0x18u, 0x01u),
        Sopp(0x1cu, 0x00u),
        Sop1(0x20u, 0u, 0x20u, 8u),
    });
    const auto cfg = Build(program);
    Require(cfg.FindBlockByProgramCounter(0x00u).terminator.kind == TerminatorKind::Branch);
    Require(cfg.FindBlockByProgramCounter(0x00u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x1cu).id);
    Require(cfg.FindBlockByProgramCounter(0x1cu).terminator.kind == TerminatorKind::Branch);
    Require(cfg.FindBlockByProgramCounter(0x1cu).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x18u).id);
}

static void CheckFetchCallAtEntry() {
    SwappcInfo info;
    info.fetchCallAllowed = true;
    info.userDataBaseRegister = 16u;
    info.userDataCount = 8u;
    const auto program = Program({
        Sopp(0x00u, 0x00u),
        Sop1(0x04u, 2u, 0x21u, 16u),
        Sopp(0x08u, 0x01u),
    });
    const auto cfg = Build(program, &info);
    Require(cfg.hasFetchCall);
    Require(cfg.fetchCallProgramCounter == 0x04u);
}

static void CheckUserDataCall() {
    SwappcInfo info;
    info.userDataBaseRegister = 0u;
    info.userDataCount = 16u;
    const auto program = Program({
        Sop1(0x00u, 14u, 0x03u, 4u),
        Sop1(0x04u, 15u, 0x03u, 5u),
        Sop1(0x08u, 14u, 0x21u, 14u),
        Sopp(0x0cu, 0x01u),
        Sopp(0x10u, 0x00u),
        Sop1(0x14u, 0u, 0x20u, 14u),
    });
    const auto calls = FindUserDataCalls(program, info);
    Require(calls.size() == 1u && calls.front() == UserDataCall{0x08u, 4u, 14u});
    ExpectThrow("user data s[4:5], which is resolved at dispatch", [&] { Build(program, &info); });

    const std::array<ResolvedScalarCall, 1> resolved{{{0x08u, 0x10u}}};
    SwappcInfo resolvedInfo = info;
    resolvedInfo.resolvedCalls = resolved;
    Require(FindUserDataCalls(program, resolvedInfo).empty());
    const auto cfg = Build(program, &resolvedInfo);
    Require(cfg.FindBlockByProgramCounter(0x00u).terminator.kind == TerminatorKind::Branch);
    Require(cfg.FindBlockByProgramCounter(0x00u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x10u).id);
    Require(cfg.FindBlockByProgramCounter(0x10u).terminator.kind == TerminatorKind::Branch);
    Require(cfg.FindBlockByProgramCounter(0x10u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x0cu).id);

    const auto pair = Program({
        Sop1(0x00u, 14u, 0x04u, 4u),
        Sop1(0x04u, 14u, 0x21u, 14u),
        Sopp(0x08u, 0x01u),
    });
    Require(FindUserDataCalls(pair, info) == std::vector<UserDataCall>{{0x04u, 4u, 14u}});

    const auto direct = Program({
        Sop1(0x00u, 14u, 0x21u, 4u),
        Sopp(0x04u, 0x01u),
    });
    Require(FindUserDataCalls(direct, info) == std::vector<UserDataCall>{{0x00u, 4u, 14u}});

    const auto computed = Program({
        Sop2Literal(0x00u, 14u, 0x00u, 4u, 0x10u),
        Sop1(0x08u, 15u, 0x03u, 5u),
        Sop1(0x0cu, 14u, 0x21u, 14u),
        Sopp(0x10u, 0x01u),
    });
    Require(FindUserDataCalls(computed, info).empty());
    try {
        Build(computed, &info);
        throw std::runtime_error("computed target built");
    } catch (const std::invalid_argument& error) {
        Require(std::string(error.what()).find("not statically resolvable") != std::string::npos);
        Require(std::string(error.what()).find("resolved at dispatch") == std::string::npos);
    }

    const auto overwritten = Program({
        Sop1(0x00u, 4u, 0x03u, 6u),
        Sop1(0x04u, 14u, 0x03u, 4u),
        Sop1(0x08u, 15u, 0x03u, 5u),
        Sop1(0x0cu, 14u, 0x21u, 14u),
        Sopp(0x10u, 0x01u),
    });
    Require(FindUserDataCalls(overwritten, info).empty());

    SwappcInfo narrow = info;
    narrow.userDataCount = 5u;
    Require(FindUserDataCalls(program, narrow).empty());

    const std::array<ResolvedScalarCall, 1> misaligned{{{0x08u, 0x12u}}};
    SwappcInfo misalignedInfo = info;
    misalignedInfo.resolvedCalls = misaligned;
    ExpectThrow("is not an instruction boundary", [&] { Build(program, &misalignedInfo); });

    const auto clobbered = Program({
        Sop1(0x00u, 14u, 0x03u, 4u),
        Sop1(0x04u, 15u, 0x03u, 5u),
        Sop1(0x08u, 14u, 0x21u, 14u),
        Sopp(0x0cu, 0x01u),
        Sop1(0x10u, 14u, 0x03u, 4u),
        Sop1(0x14u, 0u, 0x20u, 14u),
    });
    ExpectThrow("escapes the constant-offset call/return model (used at program counter 0x00000010)", [&] { Build(clobbered, &resolvedInfo); });
}

static void CheckSharedLinkCalls() {
    SwappcInfo info;
    info.userDataBaseRegister = 0u;
    info.userDataCount = 16u;
    const auto program = Program({
        Sop1(0x00u, 14u, 0x03u, 4u),
        Sop1(0x04u, 15u, 0x03u, 5u),
        Sop1(0x08u, 14u, 0x21u, 14u),
        Sop1(0x0cu, 14u, 0x03u, 8u),
        Sop1(0x10u, 15u, 0x03u, 9u),
        Sop1(0x14u, 14u, 0x21u, 14u),
        Sop1(0x18u, 14u, 0x03u, 8u),
        Sop1(0x1cu, 15u, 0x03u, 9u),
        Sop1(0x20u, 14u, 0x21u, 14u),
        Sopp(0x24u, 0x01u),
        Sopp(0x28u, 0x00u),
        Sop1(0x2cu, 0u, 0x20u, 14u),
        Sopp(0x30u, 0x00u),
        Sop1(0x34u, 0u, 0x20u, 14u),
        Sopp(0x38u, 0x00u),
        Sop1(0x3cu, 0u, 0x20u, 14u),
    });
    Require(FindUserDataCalls(program, info) == std::vector<UserDataCall>{{0x08u, 4u, 14u}, {0x14u, 8u, 14u}, {0x20u, 8u, 14u}});
    const std::array<ResolvedScalarCall, 3> resolved{{{0x08u, 0x28u}, {0x14u, 0x30u}, {0x20u, 0x38u}}};
    SwappcInfo resolvedInfo = info;
    resolvedInfo.resolvedCalls = resolved;
    const auto cfg = Build(program, &resolvedInfo);
    Require(cfg.FindBlockByProgramCounter(0x00u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x28u).id);
    Require(cfg.FindBlockByProgramCounter(0x28u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x0cu).id);
    Require(cfg.FindBlockByProgramCounter(0x0cu).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x30u).id);
    Require(cfg.FindBlockByProgramCounter(0x30u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x18u).id);
    Require(cfg.FindBlockByProgramCounter(0x18u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x38u).id);
    Require(cfg.FindBlockByProgramCounter(0x38u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x24u).id);

    const std::array<ResolvedScalarCall, 3> shared{{{0x08u, 0x28u}, {0x14u, 0x30u}, {0x20u, 0x30u}}};
    SwappcInfo sharedInfo = info;
    sharedInfo.resolvedCalls = shared;
    ExpectThrow("call regions sharing link register s[14] overlap", [&] { Build(program, &sharedInfo); });

    const auto entered = Program({
        Sopp(0x00u, 0x02u, 0x0002u),
        Sop1(0x04u, 14u, 0x03u, 4u),
        Sop1(0x08u, 15u, 0x03u, 5u),
        Sopp(0x0cu, 0x00u),
        Sop1(0x10u, 14u, 0x21u, 14u),
        Sopp(0x14u, 0x01u),
    });
    Require(FindUserDataCalls(entered, info).empty());
}

static void CheckUserDataOverwrittenLater() {
    SwappcInfo info;
    info.userDataBaseRegister = 0u;
    info.userDataCount = 16u;
    const auto later = Program({
        Sop1(0x00u, 84u, 0x04u, 14u),
        Sop1(0x04u, 14u, 0x03u, 0u),
        Sop1(0x08u, 15u, 0x03u, 1u),
        Sop1(0x0cu, 0u, 0x03u, 8u),
        Sop1(0x10u, 14u, 0x21u, 14u),
        Sopp(0x14u, 0x01u),
        Sopp(0x18u, 0x00u),
        Sop1(0x1cu, 0u, 0x20u, 14u),
    });
    Require(FindUserDataCalls(later, info) == std::vector<UserDataCall>{{0x10u, 0u, 14u}});
    const std::array<ResolvedScalarCall, 1> resolved{{{0x10u, 0x18u}}};
    SwappcInfo resolvedInfo = info;
    resolvedInfo.resolvedCalls = resolved;
    const auto cfg = Build(later, &resolvedInfo);
    Require(cfg.FindBlockByProgramCounter(0x00u).terminator.trueBlock == cfg.FindBlockByProgramCounter(0x18u).id);

    const auto looped = Program({
        Sop1(0x00u, 14u, 0x03u, 0u),
        Sop1(0x04u, 15u, 0x03u, 1u),
        Sop1(0x08u, 0u, 0x03u, 8u),
        Sop1(0x0cu, 14u, 0x21u, 14u),
        Sopp(0x10u, 0x02u, 0xfffbu),
        Sopp(0x14u, 0x01u),
    });
    Require(FindUserDataCalls(looped, info).empty());

    const auto guarded = Program({
        Sop1(0x00u, 14u, 0x03u, 0u),
        Sop1(0x04u, 15u, 0x03u, 1u),
        Sopp(0x08u, 0x05u, 0x0001u),
        Sopp(0x0cu, 0x00u),
        Sop1(0x10u, 14u, 0x21u, 14u),
        Sopp(0x14u, 0x01u),
    });
    Require(FindUserDataCalls(guarded, info) == std::vector<UserDataCall>{{0x10u, 0u, 14u}});

    const auto readAfter = Program({
        Sop1(0x00u, 14u, 0x03u, 0u),
        Sop1(0x04u, 15u, 0x03u, 1u),
        Sop1(0x08u, 14u, 0x21u, 14u),
        Sop1(0x0cu, 84u, 0x04u, 14u),
        Sopp(0x10u, 0x01u),
        Sopp(0x14u, 0x00u),
        Sop1(0x18u, 0u, 0x20u, 14u),
    });
    const std::array<ResolvedScalarCall, 1> resolvedAfter{{{0x08u, 0x14u}}};
    SwappcInfo afterInfo = info;
    afterInfo.resolvedCalls = resolvedAfter;
    ExpectThrow("escapes the constant-offset call/return model", [&] { Build(readAfter, &afterInfo); });
}

static void CheckSubroutineDecode() {
    constexpr std::array<std::uint32_t, 4> subroutine{0xbf800000u, 0xbe80200eu, 0xdeadbeefu, 0xdeadbeefu};
    const auto decoded = DecodeRdnaSubroutine(subroutine, 14u);
    Require(decoded.instructions.size() == 2u && decoded.code.size() == 2u);
    Require(decoded.instructions.back().op == RdnaOpcode::SSetpcB64);

    constexpr std::array<std::uint32_t, 3> branched{0xbf840001u, 0xbe80200eu, 0xbe80200eu};
    Require(DecodeRdnaSubroutine(branched, 14u).code.size() == 3u);

    constexpr std::array<std::uint32_t, 2> otherLink{0xbf800000u, 0xbe802008u};
    ExpectThrow("program-counter-relative", [&] { DecodeRdnaSubroutine(otherLink, 14u); });
    constexpr std::array<std::uint32_t, 3> relative{0xbe8e1f00u, 0xbf800000u, 0xbe80200eu};
    ExpectThrow("program-counter-relative", [&] { DecodeRdnaSubroutine(relative, 14u); });
    constexpr std::array<std::uint32_t, 2> ended{0xbf810000u, 0xbe80200eu};
    ExpectThrow("program-counter-relative", [&] { DecodeRdnaSubroutine(ended, 14u); });
    constexpr std::array<std::uint32_t, 1> unterminated{0xbf800000u};
    try {
        DecodeRdnaSubroutine(unterminated, 14u);
        throw std::runtime_error("unterminated subroutine decoded");
    } catch (const std::out_of_range&) {
    }

    constexpr std::array<std::uint32_t, 3> appended{0xbf810000u, 0xbf800000u, 0xbe80200eu};
    Require(RdnaInstructionDecoder{}.Decode(appended).instructions.size() == 1u);
    constexpr std::array<std::uint32_t, 1> targets{4u};
    Require(RdnaInstructionDecoder{}.Decode(appended, targets).instructions.size() == 3u);
    constexpr std::array<std::uint32_t, 1> outside{12u};
    try {
        static_cast<void>(RdnaInstructionDecoder{}.Decode(appended, outside));
        throw std::runtime_error("target outside the code decoded");
    } catch (const std::out_of_range&) {
    }
}

static void CheckThrows() {
    ExpectThrow("computed/data-dependent s_swappc_b64", [] {
        Build(Program({
            Sop1(0x00u, 8u, 0x21u, 4u),
            Sopp(0x04u, 0x01u),
        }));
    });
    ExpectThrow("escapes the constant-offset call/return model", [] {
        Build(Program({
            Sop1(0x00u, 4u, 0x1fu, 0u),
            Sop2Literal(0x04u, 4u, 0x00u, 4u, 0x18u),
            Sop2Literal(0x0cu, 5u, 0x04u, 5u, 0u),
            Sop1(0x14u, 8u, 0x21u, 4u),
            Sop1(0x18u, 8u, 0x03u, 8u),
            Sopp(0x1cu, 0x01u),
            Sopp(0x20u, 0x00u),
            Sop1(0x24u, 0u, 0x20u, 8u),
        }));
    });
    ExpectThrow("no paired s_setpc_b64 return", [] {
        Build(Program({
            Sop1(0x00u, 4u, 0x1fu, 0u),
            Sop2Literal(0x04u, 4u, 0x00u, 4u, 0x18u),
            Sop2Literal(0x0cu, 5u, 0x04u, 5u, 0u),
            Sop1(0x14u, 8u, 0x21u, 4u),
            Sopp(0x18u, 0x01u),
            Sopp(0x1cu, 0x00u),
        }));
    });
    ExpectThrow("multiple s_setpc_b64 returns", [] {
        Build(Program({
            Sop1(0x00u, 4u, 0x1fu, 0u),
            Sop2Literal(0x04u, 4u, 0x00u, 4u, 0x18u),
            Sop2Literal(0x0cu, 5u, 0x04u, 5u, 0u),
            Sop1(0x14u, 8u, 0x21u, 4u),
            Sopp(0x18u, 0x01u),
            Sopp(0x1cu, 0x00u),
            Sop1(0x20u, 0u, 0x20u, 8u),
            Sop1(0x24u, 0u, 0x20u, 8u),
        }));
    });
    ExpectThrow("is shared with another call", [] {
        Build(Program({
            Sop1(0x00u, 4u, 0x1fu, 0u),
            Sop2Literal(0x04u, 4u, 0x00u, 4u, 0x18u),
            Sop2Literal(0x0cu, 5u, 0x04u, 5u, 0u),
            Sop1(0x14u, 8u, 0x21u, 4u),
            Sop1(0x18u, 8u, 0x21u, 4u),
            Sopp(0x1cu, 0x01u),
            Sopp(0x20u, 0x00u),
            Sop1(0x24u, 0u, 0x20u, 8u),
        }));
    });
    ExpectThrow("recursive scalar call", [] {
        Build(Program({
            Sop1(0x00u, 4u, 0x1fu, 0u),
            Sop2Literal(0x04u, 4u, 0x00u, 4u, 0x10u),
            Sop2Literal(0x0cu, 5u, 0x04u, 5u, 0u),
            Sop1(0x14u, 8u, 0x21u, 4u),
            Sopp(0x18u, 0x01u),
            Sop1(0x1cu, 0u, 0x20u, 8u),
        }));
    });
    ExpectThrow("computed/data-dependent s_swappc_b64", [] {
        SwappcInfo info;
        info.fetchCallAllowed = true;
        info.userDataBaseRegister = 16u;
        info.userDataCount = 8u;
        Build(Program({
            Sopp(0x00u, 0x00u),
            Sop1(0x04u, 2u, 0x21u, 4u),
            Sopp(0x08u, 0x01u),
        }), &info);
    });
    ExpectThrow("must live in the fetch-shader code", [] {
        SwappcInfo info;
        info.fetchCallAllowed = true;
        info.userDataBaseRegister = 16u;
        info.userDataCount = 8u;
        Build(Program({
            Sopp(0x00u, 0x00u),
            Sop1(0x04u, 2u, 0x21u, 16u),
            Sopp(0x08u, 0x01u),
            Sop1(0x0cu, 0u, 0x20u, 2u),
        }), &info);
    });
}

int main() {
    try {
        CheckDecodeIdentity();
        CheckLinkModelsNextInstructionAddress();
        CheckStaticCallRegion();
        CheckFetchCallAtEntry();
        CheckUserDataCall();
        CheckSharedLinkCalls();
        CheckUserDataOverwrittenLater();
        CheckSubroutineDecode();
        CheckThrows();
    } catch (const std::exception& error) {
        std::fprintf(stderr, "scalar swappc regression: %s\n", error.what());
        return 1;
    }
    return 0;
}
