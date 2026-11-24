import Mathlib
import PEqualNP.Defs

-- A sparse search on twenty-five pairs of supplied OR signals.
-- Seventeen representatives require every wire from zero through twenty-three.
-- The other eight may omit one specific primary wire each.
theorem PEqualNP.Outside.R_meta_3022_24
    (sparse :
      let rep := fun (r : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 2, decide (∃ i : Fin 9, r.testBit i.val = true ∧ x i = true)]
      let F := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ r ∈ ([3,9,17,33,65,129,257,10,18,66,258,7,24,40,72,136,264,13,80,144,272,21,320,69,261] : List ℕ), ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size = 13 →
        D.output = 23 → (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) →
        (∀ i < 24, (i ≠ 0 ∨ r ∉ ([3,9,129] : List ℕ)) → (i ≠ 9 ∨ r ∉ ([7,13,21,69,261] : List ℕ)) → i ∈ (D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs)) →
        ∃ x, D.eval (rep r x) ≠ F x)
    (canonical :
      let rep := fun (r : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 2, decide (∃ i : Fin 9, r.testBit i.val = true ∧ x i = true)]
      let original := fun (pins : List (Fin 11)) (x : Fin 9 → Bool) => let w := List.ofFn x ++ [x 0 || x 2]; w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (pins.map fun i => w.getD i.val false)]
      let F := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (pins : List (Fin 11)), pins.length ≤ 2 → ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → (∀ x, C.eval (original pins x) = F x) →
        ∃ r ∈ ([3,9,17,33,65,129,257,10,18,66,258,7,24,40,72,136,264,13,80,144,272,21,320,69,261] : List ℕ), ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ C.size ∧
          (∀ x, D.eval (rep r x) = F x) ∧
          (∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1) ∧
          (∀ j < D.size, 11 + j ∈ D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs) ∧
          (0 < D.size → D.output = 11 + (D.size - 1)))
    (short : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → (15 : ℕ) ≤ x1.size)
    (requiredInputs :
      let rep := fun (r : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 2, decide (∃ i : Fin 9, r.testBit i.val = true ∧ x i = true)]
      let F := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      (∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo E → PEqualNP.MetaComplexity.circuitFun 9 E = F → 15 ≤ E.size) →
      ∀ r ∈ ([3,9,17,33,65,129,257,10,18,66,258,7,24,40,72,136,264,13,80,144,272,21,320,69,261] : List ℕ), ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
        (∀ x, D.eval (rep r x) = F x) →
        D.size = 13 ∧ ∀ i < 11, (i ≠ 0 ∨ r ∉ ([3,9,129] : List ℕ)) → (i ≠ 9 ∨ r ∉ ([7,13,21,69,261] : List ℕ)) → i ∈ (D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs)) :
    ∀ (x1 : List (Fin (11 : ℕ))),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : Fin (11 : ℕ)) => x7.getD (↑x8) Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hp C hf hs
  let rep := fun (r : ℕ) (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 2, decide (∃ i : Fin 9, r.testBit i.val = true ∧ x i = true)]
  let original := fun (pins : List (Fin 11)) (x : Fin 9 → Bool) => let w := List.ofFn x ++ [x 0 || x 2]; w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (pins.map fun i => w.getD i.val false)]
  let F := fun (x : Fin 9 → Bool) => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have edge (x : Fin 9 → Bool) : F x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    simp only [F, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  by_contra! counter
  have correct : ∀ x, C.eval (original pins x) = F x := by
    intro x
    rw [edge]
    exact Classical.not_not.mp (counter x)
  obtain ⟨r, hr, D, hD, bound, cD, unary, gateUse, last⟩ := canonical pins hp C hf correct
  have lower (E : PEqualNP.CircuitLowerBounds.Circuit) (hE : PEqualNP.MetaComplexity.FanInTwo E)
      (he : PEqualNP.MetaComplexity.circuitFun 9 E = F) : 15 ≤ E.size := by
    apply short E hE
    exact he.trans (funext edge)
  obtain ⟨size, rawUse⟩ := requiredInputs lower r hr D hD (bound.trans hs) cD
  have allUse : ∀ i < 24, (i ≠ 0 ∨ r ∉ ([3,9,129] : List ℕ)) → (i ≠ 9 ∨ r ∉ ([7,13,21,69,261] : List ℕ)) → i ∈ (D.output :: D.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs) := by
    intro i hi exceptional triple
    by_cases raw : i < 11
    · exact rawUse i raw exceptional triple
    · have body := gateUse (i-11) (by omega)
      rwa [show 11 + (i-11) = i by omega] at body
  have out : D.output = 23 := by simpa [size] using last (by omega)
  obtain ⟨x, hx⟩ := sparse r hr D hD size out unary allUse
  exact hx (cD x)
