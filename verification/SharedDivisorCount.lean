module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorization.Basic

/-! # Counting pairs in an arithmetic tube with a shared divisor

For a target `z` and divisor `p`, write `x = p*u`. The tube becomes
`k*u ≤ y ≤ k*u + W` with `k = A*p` and `y = B*z`. Dividing by `k`
places `u` within `W/k` of `y/k`. All variables and divisions are natural.
-/

public section

namespace SharedDivisorCount

/-- The allowed multipliers at a fixed target. -/
private def multipliers (k y W : ℕ) : Finset ℕ :=
  (Finset.Iic (y / k)).filter fun u => y ≤ k * u + W

private theorem mem_multipliers {k y W u : ℕ} (hk : 0 < k) :
    u ∈ multipliers k y W ↔ k * u ≤ y ∧ y ≤ k * u + W := by
  simp only [multipliers, Finset.mem_filter, Finset.mem_Iic, Nat.le_div_iff_mul_le hk]
  rw [Nat.mul_comm u k]

private theorem card_multipliers_le (k y W : ℕ) (hk : 0 < k) :
    (multipliers k y W).card ≤ 1 + W / k := by
  have sub : multipliers k y W ⊆ Finset.Icc (y / k - W / k) (y / k) := by
    intro u hu
    obtain ⟨hlo, hhi⟩ := Finset.mem_filter.mp hu
    have h : y / k ≤ W / k + u := calc
      y / k ≤ (W + k * u) / k := Nat.div_le_div_right (by simpa [Nat.add_comm] using hhi)
      _ = W / k + u := Nat.add_mul_div_left W u hk
    exact Finset.mem_Icc.mpr ⟨by omega, Finset.mem_Iic.mp hlo⟩
  have length_bound (q s : ℕ) : q + 1 - (q - s) ≤ 1 + s := by omega
  exact (Finset.card_le_card sub).trans (by rw [Nat.card_Icc]; apply length_bound)

/-- Actual pairs `(x,z)` for one divisor, with `z` in the eligible target set `E`. -/
def pairsFor (A B W p : ℕ) (E : Finset ℕ) : Finset (ℕ × ℕ) :=
  (E.filter (p ∣ ·)).biUnion fun z =>
    (multipliers (A * p) (B * z) W).image fun u => (p * u, z)

theorem mem_pairsFor {A B W p x z : ℕ} {E : Finset ℕ} (hA : 0 < A) (hp : 0 < p) :
    (x, z) ∈ pairsFor A B W p E ↔
      z ∈ E ∧ p ∣ z ∧ p ∣ x ∧ A * x ≤ B * z ∧ B * z ≤ A * x + W := by
  simp only [pairsFor, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image,
    mem_multipliers (Nat.mul_pos hA hp), Nat.mul_assoc, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨hz, hpz⟩, u, ⟨hlo, hhi⟩, rfl, rfl⟩
    exact ⟨hz, hpz, ⟨u, rfl⟩, hlo, hhi⟩
  · rintro ⟨hz, hpz, ⟨u, rfl⟩, hlo, hhi⟩
    exact ⟨z, ⟨hz, hpz⟩, u, ⟨hlo, hhi⟩, rfl, rfl⟩

/-- Count only the eligible targets divisible by `p`; each costs at most one short interval. -/
theorem card_pairsFor_le (A B W p : ℕ) (E : Finset ℕ) (hA : 0 < A) (hp : 0 < p) :
    (pairsFor A B W p E).card ≤ (E.filter (p ∣ ·)).card * (1 + W / (A * p)) := by
  unfold pairsFor
  calc
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ E.filter (p ∣ ·), (1 + W / (A * p)) :=
      Finset.sum_le_sum fun z _ =>
        Finset.card_image_le.trans (card_multipliers_le (A * p) (B * z) W (Nat.mul_pos hA hp))
    _ = _ := by simp

/-- Single-divisor count over all positive targets through `Z`. -/
theorem card_pairsFor_upto_le (A B W p Z : ℕ) (hA : 0 < A) (hp : 0 < p) :
    (pairsFor A B W p (Finset.Ioc 0 Z)).card ≤ (Z / p) * (1 + W / (A * p)) := by
  simpa only [Nat.Ioc_filter_dvd_card_eq_div] using card_pairsFor_le A B W p (Finset.Ioc 0 Z) hA hp

/-- Union of solution pairs, not a set of triples marked by the witnessing divisor. -/
def sharedPairs (A B W : ℕ) (E D : Finset ℕ) : Finset (ℕ × ℕ) :=
  D.biUnion fun p => pairsFor A B W p E

theorem mem_sharedPairs {A B W x z : ℕ} {E D : Finset ℕ} (hA : 0 < A)
    (hD : ∀ p ∈ D, 0 < p) :
    (x, z) ∈ sharedPairs A B W E D ↔ z ∈ E ∧ A * x ≤ B * z ∧ B * z ≤ A * x + W ∧
      ∃ p ∈ D, p ∣ x ∧ p ∣ z := by
  rw [sharedPairs, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, h⟩
    obtain ⟨hz, hpz, hpx, hlo, hhi⟩ := (mem_pairsFor hA (hD p hp)).mp h
    exact ⟨hz, hlo, hhi, p, hp, hpx, hpz⟩
  · rintro ⟨hz, hlo, hhi, p, hp, hpx, hpz⟩
    exact ⟨p, hp, (mem_pairsFor hA (hD p hp)).mpr ⟨hz, hpz, hpx, hlo, hhi⟩⟩

/-- The same bound works for arbitrary finite `E`, in particular for sets of positive targets. -/
theorem card_sharedPairs_le (A B W : ℕ) (E D : Finset ℕ) (hA : 0 < A)
    (hD : ∀ p ∈ D, 0 < p) :
    (sharedPairs A B W E D).card ≤ ∑ p ∈ D, (E.filter (p ∣ ·)).card * (1 + W / (A * p)) :=
  Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p hp => card_pairsFor_le A B W p E hA (hD p hp)

/-- Forgetting the later target `z` charges no extra multiplicity. -/
theorem card_sourceProjection_le (A B W : ℕ) (E D : Finset ℕ) (hA : 0 < A)
    (hD : ∀ p ∈ D, 0 < p) :
    ((sharedPairs A B W E D).image Prod.fst).card ≤
      ∑ p ∈ D, (E.filter (p ∣ ·)).card * (1 + W / (A * p)) :=
  Finset.card_image_le.trans (card_sharedPairs_le A B W E D hA hD)

end SharedDivisorCount
