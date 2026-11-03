module

public import VM.Basic
public import VM.Byte
public import VM.Adder
public import VM.Multiplier
public import VM.Cpu
public import VM.Ensemble

/-!
# A toy VM in Clean

A toy machine with every piece a real chip has: a precomputed table served as a bus, two
chips that pull from it and push their results on buses of their own, a CPU that selects
which bus to pull from, and the ensemble theorem that ties the tables together.

Read in this order.

1. `Basic`: the field and the lemmas that lift a field identity to the naturals.
2. `Byte`: the 256 byte values as a static lookup channel.
3. `Adder`: the first chip. Bus `ADD`, `Row`, `main`, `Spec`, `Honest`, `lift`, and the two
   proofs, soundness and completeness.
4. `Multiplier`: the second chip, same shape with a quadratic identity and a two-limb result.
5. `Cpu`: the consumer. Two selector bits, one `pullIf` per bus, a conditional `Spec`.
6. `Ensemble`: the machine. `pushStatic` serves the byte list as a table, then four tables
   and three channels in dependency order, and `cpu_rows_correct`: constraints plus balanced
   buses imply every CPU row holds the result of the operation it selected.

What to try. Each edit first breaks the `obtain` or `refine` pattern that unpacks the
hypotheses, since the list of operations changed; fix the pattern and look at what is left.

- Remove `isBit r.carry` from the adder: `soundness` is left needing `IsBool carry` for
  `lift`, with nothing to build it from. The row `a = 1, b = 1, sum = 0, carry = 2/256` gets
  through: every value is a byte and the identity holds in the field.
- Make the `ADD` guarantee something the adder cannot prove, say `sum.val = a.val + b.val`
  without the modulus: the push obligation in the adder's `soundness` fails.
- Drop the byte bounds from the `ADD` guarantee: the adder still keeps it, and the CPU's
  proofs close once they stop unpacking the bounds, because `Cpu.Spec` never needed them. A
  consumer whose `Spec` did need them could not be fixed.
- Remove `assertZero (r.is_add * r.is_mul)` from the CPU: every obligation still closes. The
  two pulls are independent, so a row may select both.
- Remove `isBit r.is_add` from the CPU: `requirementsChannelsLawful` is left with
  `is_add ≠ 1 → is_add ≠ 0 → AddBus.Guarantees …`, which is unprovable. A multiplicity
  that is neither `0` nor `-1` is not a pull.
-/
