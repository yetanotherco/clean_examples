module

public import VM.Cpu
public import Clean.Air.OrderedChannel

@[expose] public section

/-!
# The whole toy machine

Four tables and three buses, in dependency order: the byte table provides `BYTE`, the adder
and the multiplier pull from `BYTE` and provide `ADD` and `MUL`, the CPU pulls from both. The
theorem at the end is what the verifier's acceptance means: constraints plus balanced buses
imply every CPU row holds the result of the operation it selected.
-/

namespace VM
open Air.Flat

/-- A static lookup channel served as a table of the machine. A flat AIR has no preprocessed
columns, so a row cannot carry a fixed value; instead every row carries one multiplicity
column per entry and pushes the whole list with those multiplicities. The prover may use any
number of such rows. -/
def pushStatic {Message : TypeMap} [ProvableType Message] (slc : StaticLookupChannel (F p) Message)
    [NeZero slc.table.length] : GeneralFormalCircuit (F p) (fields slc.table.length) unit where
  main mults := do
    let _ ← Circuit.mapFinRange slc.table.length fun i =>
      (Channel.fromStatic (F p) Message slc).emit mults[i] (const slc.table[i])
  channelsWithRequirements := [(Channel.fromStatic (F p) Message slc).toRaw]
  Spec _ _ _ := True
  soundness := by
    circuit_proof_start
    intro i _ _
    exact (slc.guarantees_iff _).mpr (List.getElem_mem _)
  completeness := by circuit_proof_start

-- Stated generically: unfolding `pushStatic` on the concrete 256-entry table does not terminate.
lemma pushStatic_channelsWithGuarantees {Message : TypeMap} [ProvableType Message]
    (slc : StaticLookupChannel (F p) Message) [NeZero slc.table.length] :
    (pushStatic slc).channelsWithGuarantees = [] := by
  simp [circuit_norm, pushStatic]

instance : NeZero byteTable.table.length := ⟨by simp [byteTable]⟩

def ensemble : SoundEnsemble (F p) unit :=
  SoundEnsemble.empty (F p) unit
  |>.addTable ⟨pushStatic byteTable⟩
      (by rw [pushStatic_channelsWithGuarantees]; simp)
      (by simp [circuit_norm])
  |>.addFinishedChannel Byte.toRaw
  |>.addTable ⟨Adder.circuit⟩
      (by simp [circuit_norm, Adder.circuit, byteTable])
      (by simp [circuit_norm, Adder.circuit, AddBus, byteTable])
  |>.addFinishedChannel AddBus.toRaw
  |>.addTable ⟨Multiplier.circuit⟩
      (by simp [circuit_norm, Multiplier.circuit, byteTable])
      (by simp [circuit_norm, Multiplier.circuit, MulBus, AddBus, byteTable])
  |>.addFinishedChannel MulBus.toRaw
  |>.addTable ⟨Cpu.circuit⟩
      (by simp [circuit_norm, Cpu.circuit, AddBus, MulBus])
      (by simp [circuit_norm, Cpu.circuit, AddBus, MulBus])

/-- If every table's constraints hold and every bus balances, every CPU row has the right
result for the operation it selected. The buses turn the chips' promises and the CPU's
assumptions into facts. -/
theorem cpu_rows_correct (witness : EnsembleWitness ensemble.ensemble)
    (hc : witness.Constraints) (hb : witness.BalancedChannels) :
    ∀ table ∈ witness.tables, table.component = ⟨Cpu.circuit⟩ →
      ∀ row ∈ table.table, Cpu.Spec (valueFromOffset Cpu.Row 0 (table.environment row)) := by
  have hsound : ensemble.ensemble.TableSoundness :=
    Ensemble.tableSoundness_of_soundChannels
      ⟨ensemble.finished, ensemble.finished_subset, ensemble.soundChannels⟩
  -- No table assumes anything at the ensemble level.
  have hassume : witness.Assumptions := by
    intro table htable
    have hmem := EnsembleWitness.mem_allTables_component_of_mem_allTables htable
    simp only [circuit_norm, ensemble, Ensemble.allTables, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    obtain ⟨comp, width, tbl, data, uw⟩ := table
    simp only at hmem
    intro row _
    aesop (add safe (by exact trivial))
  have hspec := hsound witness hassume hc hb
  intro table htable hcomp row hrow
  have := hspec table (witness.mem_allTables_of_mem_tables htable) row hrow
  obtain ⟨comp, width, tbl, data, uw⟩ := table
  simp only at hcomp
  subst hcomp
  exact this

end VM
