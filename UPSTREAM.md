# Source record

This directory contains the ArgoMAC source, proofs, and tests.
The source comes from https://github.com/SebastianElvis/argomac-lean.
The original baseline commit is `711689cd0253edece8d0c617ad5a7afaa937673e`.
The last source commit before this copy is `6544216f4c50bf846775fa27f1556bdf7e064bf7`.
This copy also includes the pending proof changes from that checkout.
This repository now records further changes in the same commits as the challenge.

The `baseline` field in `../challenge.yaml` selects this directory.
The local acceptance test uses this directory.
`Submission.solution` proves the complete adaptive privacy obligation.

The copy excludes Git metadata, dependency downloads, and build output.
The local Lake configuration uses the challenge library in `..`.

The source check covers all 956 source files from the previous checkout.
The local copy contains every file from that set.
The local copy also contains the later proof fixes.
The previous `BudgetAudit.lean` is now `tests/ProofAudit.lean`.
The memory layout proofs from `LayoutCheck.lean` already appear in `Proof/Privacy/Simulator/Arithmetic/MemoryLayout.lean`.
The protocol checks from `ProtocolCheck.lean` already appear in `Proof/Privacy/Simulator/Arithmetic/ParsedProgramSource.lean`.

The `argomac-lean/` directory is the only starter.
The repository has no separate `starter/` directory.
The repository contains one copy of the ArgoMAC source.
