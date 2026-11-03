# clean_examples

A toy VM written in [Clean](https://github.com/Verified-zkEVM/clean), the Lean 4 library for
AIR circuits with LogUp channels. Each table is a circuit with a specification and two
proofs, soundness and completeness; the buses carry contracts between tables; an ensemble
theorem turns the per-table proofs into a statement about the whole machine.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` and Clean in `lakefile.toml`; Mathlib and CompPoly come in through Clean.

```
lake exe cache get   # Mathlib binaries
lake build           # Clean and CompPoly compile from source the first time
```

## What it has today

Four tables, three buses and one theorem: if every table's constraints hold and every bus
balances, every CPU row holds the result of the operation it selected.

| table | pulls | pushes | one row is |
|---|---|---|---|
| `BYTE` | | `BYTE` | the 256 byte values, each with a multiplicity |
| `ADDER` | `BYTE` | `ADD` | `a + b = sum + 256 · carry`, with `carry` a bit |
| `MULTIPLIER` | `BYTE` | `MUL` | `a · b = lo + 256 · hi` |
| `CPU` | `ADD` or `MUL`, by selector | | an operation, with no arithmetic of its own |

A pull assumes the bus guarantee for the message; a push owes it. The ensemble adds the
tables in that order, so every bus is finished by its provider before a consumer pulls from
it, and Clean's ordered-channel theorem turns the per-table proofs into one about the machine.

## Reading order

1. `VM/Basic.lean`: the field and the lemmas that lift a field identity to the naturals.
2. `VM/Byte.lean`: the 256 byte values as a static lookup channel.
3. `VM/Adder.lean`: the first chip. Bus `ADD`, `Row`, `main`, `Spec`, `Honest`, `lift`, and the
   two proofs, soundness and completeness.
4. `VM/Multiplier.lean`: the second chip, same shape with a quadratic identity and a two-limb
   result.
5. `VM/Cpu.lean`: the consumer. Two selector bits, one `pullIf` per bus, a conditional `Spec`.
6. `VM/Ensemble.lean`: `pushStatic` serves the byte list as a table, the ensemble lists the four
   tables and three channels, and `cpu_rows_correct` is the theorem.

## What is proved

For each chip, soundness: on every row that satisfies the constraints, `Spec` holds and every
pushed message meets its bus guarantee. And completeness: the row the honest prover fills in
satisfies every constraint and every pull. For the machine:

```lean
theorem cpu_rows_correct (witness : EnsembleWitness ensemble.ensemble)
    (hc : witness.Constraints) (hb : witness.BalancedChannels) :
    ∀ table ∈ witness.tables, table.component = ⟨Cpu.circuit⟩ →
      ∀ row ∈ table.table, Cpu.Spec (valueFromOffset Cpu.Row 0 (table.environment row))
```

Bus balance is a hypothesis: it is what the lookup argument enforces in the proof system. The
proof system itself, the code that builds the traces and the code that evaluates the
constraints are outside the model. Every theorem depends only on Lean's standard axioms.
