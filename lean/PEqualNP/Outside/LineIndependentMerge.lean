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

end PEqualNP.Outside.LineIndependentMerge

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

theorem PEqualNP.Outside.LineIndependentMerge :
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
