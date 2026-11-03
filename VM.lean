module

public import VM.Basic
public import VM.Byte
public import VM.Adder
public import VM.Multiplier
public import VM.Cpu
public import VM.Ensemble

/-!
# A toy VM in Clean

Each table is a circuit with a specification and two proofs, the buses carry contracts
between tables, and an ensemble theorem turns the per-table proofs into a statement about the
whole machine. The README has what the machine contains today and the reading order.
-/
