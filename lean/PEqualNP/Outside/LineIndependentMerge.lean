import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LineIndependentMerge

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

lemma incident_of_alive {P L : ℕ} {inc : Fin P → Fin L → Bool}
    {C : Circuit} {g : ℕ} {w : Fin L} {p : Fin P}
    (hlow : IsLow P L inc C g w) (hp : p ∈ aliveSet P L C g w) :
    inc p w = true := by
  have hv : wireVal C (pointLineInput P L p w) g = true := by
    simpa [aliveSet] using hp
  have hs := hlow (fun q => decide (q = p)) hv
  simp only [lineSum, decide_eq_true_eq] at hs
  obtain ⟨q, hq, hqp⟩ := hs
  simpa [hqp] using hq

lemma unique_line {P L : ℕ} {inc : Fin P → Fin L → Bool}
    {C : Circuit} {g : ℕ}
    (hnofour : ∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true))
    (hind : ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g)
    {w v : Fin L} (hw : IsNewLowMerge P L inc C g w)
    (hv : IsNewLowMerge P L inc C g v) : w = v := by
  have hc : 1 < (aliveSet P L C g w).card := by
    have hi := Finset.card_image_le (s := aliveSet P L C g w)
      (f := classLabel P L inc C g w)
    have hh := hw.2
    unfold classesMet at hh
    omega
  obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp hc
  have move (r : Fin P) (hr : r ∈ aliveSet P L C g w) :
      r ∈ aliveSet P L C g v := by
    simpa only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and,
      ← hind r w v] using hr
  by_contra hne
  exact hnofour p q w v hpq hne ⟨incident_of_alive hw.1 hp,
    incident_of_alive hw.1 hq, incident_of_alive hv.1 (move p hp),
    incident_of_alive hv.1 (move q hq)⟩

lemma line_count {P L : ℕ} {inc : Fin P → Fin L → Bool}
    {C : Circuit} {g : ℕ}
    (hnofour : ∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true))
    (hind : ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g) :
    (Finset.univ.filter (fun w => IsNewLowMerge P L inc C g w)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro w hw v hv
  exact unique_line hnofour hind (Finset.mem_filter.mp hw).2
    (Finset.mem_filter.mp hv).2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem fold_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_default]; rw [fold_length]; exact h


def rd (C : Circuit) (x : List Bool) (g i : ℕ) : Bool :=
  if i < g then (C.wires x).getD i false else false

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := fold_length _ _

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (C.wires x).getD i false = x.getD i false := fold_getD_lt _ _ _ h

theorem wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false
      = C.gates[j].op.eval (C.gates[j].inputs.map fun i => rd C x (x.length + j) i) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp
  set A := (C.gates.take j).foldl step x with hA
  have hAl : A.length = x.length + j := by
    rw [hA, fold_length]; simp; omega
  have hw : C.wires x = (C.gates.drop (j + 1)).foldl step (step A C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hreadA : ∀ i, A.getD i false = rd C x (x.length + j) i := by
    intro i
    unfold rd
    by_cases hi : i < x.length + j
    · rw [if_pos hi, hw, fold_getD_lt _ (step A C.gates[j]) i (by simp [step]; omega), step,
        List.getD_append _ _ _ _ (by omega)]
    · rw [if_neg hi, List.getD_eq_default]; omega
  rw [hw, fold_getD_lt _ _ _ (by simp [step]; omega), step,
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [hAl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  congr 1
  exact List.map_congr_left (fun i _ => hreadA i)

lemma or_read {P L : ℕ} {C : Circuit} {g a b : ℕ}
    (hidx : P + L ≤ g) (ha : a < g) (hb : b < g)
    (hgate : C.gates[g - (P + L)]? = some ⟨GateOp.or, [a, b]⟩)
    (p : Fin P) (w : Fin L) :
    wireVal C (pointLineInput P L p w) g =
      (wireVal C (pointLineInput P L p w) a ||
        wireVal C (pointLineInput P L p w) b) := by
  obtain ⟨hj, hg⟩ := List.getElem?_eq_some_iff.mp hgate
  have h := wires_gate C (pointLineInput P L p w) (g - (P + L)) hj
  have hlen : (pointLineInput P L p w).length = P + L := by
    simp [pointLineInput, restrictInput]
  rw [hlen, Nat.add_sub_of_le hidx, hg] at h
  simpa [GateOp.eval, rd, ha, hb, wireVal] using h

lemma plain_unique {P L : ℕ} {inc : Fin P → Fin L → Bool}
    {C : Circuit} {g : ℕ}
    (hnofour : ∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true))
    (hind : ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g)
    {w v : Fin L} (hw : IsLowMerge P L inc C g w)
    (hv : IsLowMerge P L inc C g v) : w = v := by
  obtain ⟨hidx, a, ha, b, hb, hg, hlow, hab, hba⟩ := hw
  obtain ⟨p, hp, hpb⟩ := Finset.not_subset.mp hab
  obtain ⟨q, hq, hqa⟩ := Finset.not_subset.mp hba
  have hpq : p ≠ q := by intro h; subst q; exact hqa hp
  have hgp : p ∈ aliveSet P L C g w := by
    simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [or_read hidx ha hb hg, hp]
    rfl
  have hgq : q ∈ aliveSet P L C g w := by
    simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [or_read hidx ha hb hg, hq]
    simp
  have move (r : Fin P) (hr : r ∈ aliveSet P L C g w) :
      r ∈ aliveSet P L C g v := by
    simpa only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and,
      ← hind r w v] using hr
  obtain ⟨_, _, _, _, _, _, hlowv, _, _⟩ := hv
  by_contra hne
  exact hnofour p q w v hpq hne ⟨incident_of_alive hlow hgp,
    incident_of_alive hlow hgq, incident_of_alive hlowv (move p hgp),
    incident_of_alive hlowv (move q hgq)⟩

lemma plain_count {P L : ℕ} {inc : Fin P → Fin L → Bool}
    {C : Circuit} {g : ℕ}
    (hnofour : ∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true))
    (hind : ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g) :
    (Finset.univ.filter (fun w => IsLowMerge P L inc C g w)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro w hw v hv
  exact plain_unique hnofour hind (Finset.mem_filter.mp hw).2
    (Finset.mem_filter.mp hv).2

lemma sum_new :
    ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (S : Finset ℕ),
    (∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true)) →
    (∀ g ∈ S, ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g) →
    (∑ w : Fin L, (S.filter (fun g => IsNewLowMerge P L inc C g w)).card) ≤ S.card := by
  intro P L inc C S hnofour hind
  calc
    (∑ w : Fin L, (S.filter (fun g => IsNewLowMerge P L inc C g w)).card) =
        ∑ g ∈ S, (Finset.univ.filter (fun w => IsNewLowMerge P L inc C g w)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ g ∈ S, 1 := Finset.sum_le_sum fun g hg =>
      PEqualNP.Outside.LineIndependentMerge.line_count hnofour (hind g hg)
    _ = S.card := by simp

lemma sum_plain :
    ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (S : Finset ℕ),
    (∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true)) →
    (∀ g ∈ S, ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g) →
    (∑ w : Fin L, (S.filter (fun g => IsLowMerge P L inc C g w)).card) ≤ S.card := by
  intro P L inc C S hnofour hind
  calc
    (∑ w : Fin L, (S.filter (fun g => IsLowMerge P L inc C g w)).card) =
        ∑ g ∈ S, (Finset.univ.filter (fun w => IsLowMerge P L inc C g w)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ g ∈ S, 1 := Finset.sum_le_sum fun g hg =>
      PEqualNP.Outside.LineIndependentMerge.plain_count hnofour (hind g hg)
    _ = S.card := by simp

end PEqualNP.Outside.LineIndependentMerge

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

theorem PEqualNP.Outside.LineIndependentMerge :
    ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (S : Finset ℕ),
    (∀ p q : Fin P, ∀ w v : Fin L, p ≠ q → w ≠ v →
      ¬ (inc p w = true ∧ inc q w = true ∧ inc p v = true ∧ inc q v = true)) →
    (∀ g ∈ S, ∀ p : Fin P, ∀ w v : Fin L,
      wireVal C (pointLineInput P L p w) g =
        wireVal C (pointLineInput P L p v) g) →
    ((∑ w : Fin L, (S.filter (fun g => IsNewLowMerge P L inc C g w)).card) ≤ S.card) ∧
    ((∑ w : Fin L, (S.filter (fun g => IsLowMerge P L inc C g w)).card) ≤ S.card) := by
  intro P L inc C S hnofour hind
  exact ⟨PEqualNP.Outside.LineIndependentMerge.sum_new P L inc C S hnofour hind,
    PEqualNP.Outside.LineIndependentMerge.sum_plain P L inc C S hnofour hind⟩
