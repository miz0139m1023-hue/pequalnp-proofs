import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2744_8
    (short : ∀ D : Circuit, FanInTwo D → circuitFun 9 D = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) → 15 ≤ D.size)
    (accounting :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let cols := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
      (∀ D : Circuit, FanInTwo D → circuitFun 9 D=F → 15≤D.size) →
      ∀ C : Circuit, FanInTwo C → C.size≤14 → (∀ x, C.eval (cols x)=F x) →
        ∃ E : Circuit, FanInTwo E ∧ E.size=14 ∧ E.output=23 ∧
          (∀ i<24, i ∈ E.output :: E.gates.flatMap Gate.inputs) ∧
          (E.gates.filter (fun g => g.op.eval [false,false])).length≤4 ∧
          ∀ x, E.eval (cols x)=F x)
    (several :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let cols := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
      ∀ E : Circuit, FanInTwo E → E.size=14 → E.output=23 →
        (∀ i<24, i ∈ E.output :: E.gates.flatMap Gate.inputs) →
        3≤(E.gates.filter (fun g => g.op.eval [false,false])).length → (E.gates.filter (fun g => g.op.eval [false,false])).length≤4 →
        ∃ x, E.eval (cols x)≠F x)
    (few :
      let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let cols := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
      ∀ E : Circuit, FanInTwo E → E.size=14 → E.output=23 →
        (∀ i<24, i ∈ E.output :: E.gates.flatMap Gate.inputs) →
        (E.gates.filter (fun g => g.op.eval [false,false])).length≤2 →
        ∃ x, E.eval (cols x)≠F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C fc first computes second
  by_contra! small
  let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let cols := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
  have edge (x : Fin 9 → Bool) : F x = (fun x : Fin 9 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) x := by
    simp only [F,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have lo : ∀ D : Circuit, FanInTwo D → circuitFun 9 D=F → 15≤D.size := by
    intro D hf he
    exact short D hf (he.trans (funext edge))
  have keep (gs : List Gate) (l : List Bool) (i : Nat) (hi : i < l.length) :
      ((Circuit.mk gs 0).wires l).getD i false = l.getD i false := by
    induction gs generalizing l with
    | nil => rfl
    | cons g gs ih =>
      let y := g.op.eval (g.inputs.map fun j => l.getD j false)
      change ((Circuit.mk gs 0).wires (l ++ [y])).getD i false = _
      rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]
  obtain ⟨g1,h1⟩ := second
  cases hgs : C.gates with
  | nil => simp [hgs] at h1
  | cons g gs =>
    let D : Circuit := ⟨gs,C.output⟩
    have fd : FanInTwo D := fun h hh => fc h (hgs ▸ List.mem_cons_of_mem g hh)
    have sd : D.size ≤ 14 := by
      have hs : C.size = D.size+1 := by
        change C.gates.length=gs.length+1
        simp only [hgs,List.length_cons]
      omega
    have cD (x : Fin 9 → Bool) : D.eval (cols x)=F x := by
      let l := List.ofFn x
      let y := g.op.eval (g.inputs.map fun i => l.getD i false)
      have len : l.length=9 := List.length_ofFn
      have yy := first x
      change (C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun i => w.getD i false))]) l).getD 9 false = _ at yy
      simp only [hgs,List.foldl_cons] at yy
      change ((Circuit.mk gs 0).wires (l ++ [y])).getD 9 false = _ at yy
      rw [keep _ _ _ (by simp [len])] at yy
      have atNine : (l ++ [y]).getD 9 false=y := by rw [←len]; simp
      rw [atNine] at yy
      have ce := congrFun computes x
      rw [edge]
      change ((C.gates.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun i => w.getD i false))]) l).getD C.output false)=_ at ce
      simp only [hgs,List.foldl_cons] at ce
      change D.eval (l ++ [y])=_ at ce
      simpa only [cols,yy] using ce
    obtain ⟨E,hf,n,out,all,count,good⟩ := accounting lo D fd sd cD
    by_cases h : (E.gates.filter (fun g => g.op.eval [false,false])).length≤2
    · obtain ⟨x,hx⟩ := few E hf n out all h
      exact hx (good x)
    · obtain ⟨x,hx⟩ := several E hf n out all (by omega) count
      exact hx (good x)
