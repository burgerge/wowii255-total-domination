import WOWII256Family

/-! 第 256 题的最优普适系数，包括限制为二分图的情形。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax edgeNeighborhoodMax_pos_of_edge order_le_totalDomination_mul_max)

/-- 将原猜想右侧的系数 2 替换成 c。 -/
def CoefficientBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  c * ((minDegreeNeighborhood G).card : ℝ) / (edgeNeighborhoodMax G : ℝ) ≤
    G.totalDominationNumber

theorem coefficient_two_is_original {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : CoefficientBound G 2 ↔ Bound G := Iff.rfl

/-- 有限连通简单图上的有效系数。 -/
def ValidCoefficient (c : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → CoefficientBound G c

/-- 限制为连通二分图时的有效系数。 -/
def BipartiteValidCoefficient (c : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.IsBipartite → CoefficientBound G c

theorem coefficient_valid_of_le_one {c : ℝ} (hc : c ≤ 1) : ValidCoefficient c := by
  intro V _ _ _ G _ hG
  have hadj := hG.preconnected.exists_adj_of_nontrivial
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨v, hv⟩ := hadj u
  have hM : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hv
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ 1 * ((minDegreeNeighborhood G).card : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by
      rw [one_mul]
      exact_mod_cast ((Finset.card_le_univ (minDegreeNeighborhood G)).trans
        (order_le_totalDomination_mul_max G hadj))

private theorem estimate (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : m = k * k) :
    (k + 1) * (m * m + 1 + 2 * k * m) ≤ (k + 7) * (m * m) := by
  have hm₁ : 1 ≤ m := by
    rw [hm]
    exact Nat.mul_pos (by omega) (by omega)
  have h1 : m * m + 1 + 2 * k * m ≤ m * m + 3 * k * m := by
    have hkm := Nat.mul_le_mul_right m hk
    calc
      _ ≤ m * m + k * m + 2 * k * m := by omega
      _ = _ := by ring
  have h2 : (k + 1) * (3 * k * m) ≤ 6 * (m * m) := by
    calc
      _ ≤ (2 * k) * (3 * k * m) := Nat.mul_le_mul_right _ (by omega)
      _ = 6 * ((k * k) * m) := by ring
      _ = _ := by rw [← hm]
  calc
    _ ≤ (k + 1) * (m * m + 3 * k * m) := Nat.mul_le_mul_left _ h1
    _ = (k + 1) * (m * m) + (k + 1) * (3 * k * m) := by ring
    _ ≤ (k + 1) * (m * m) + 6 * (m * m) := Nat.add_le_add_left h2 _
    _ = _ := by ring

/-- 任意大于 1 的系数都存在参数化的连通二分图反例。 -/
theorem exists_bipartite_counterexample {c : ℝ} (hc : 1 < c) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ (Family.graph k m).Connected ∧
      (Family.graph k m).IsBipartite ∧ ¬ CoefficientBound (Family.graph k m) c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (7 / (c - 1))
  let k := n + 2
  let m := k * k
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hm : 1 ≤ m := Nat.mul_pos (by omega) (by omega)
  let _ : NeZero k := ⟨by omega⟩
  let _ : NeZero m := ⟨by omega⟩
  let G := Family.graph k m
  refine ⟨k, m, by omega, by omega, Family.connected k m, Family.bipartite k m, ?_⟩
  have hM := Family.maximum_pos k m
  have hgm : G.totalDominationNumber * edgeNeighborhoodMax G ≤ (k + 7) * (m * m) :=
    (Nat.mul_le_mul (Family.domination_le k m) (Family.maximum_le hk hm)).trans (estimate k hk m rfl)
  have hcard := Family.target_card_lower hk hm
  have hn' : 7 < (n : ℝ) * (c - 1) := (div_lt_iff₀ (sub_pos.mpr hc)).mp hn
  have hnk : (n : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_right n 2)
  have hkc : 7 < (k : ℝ) * (c - 1) :=
    hn'.trans_le (mul_le_mul_of_nonneg_right hnk (sub_nonneg.mpr hc.le))
  have hks : (k : ℝ) + 7 < c * k := by nlinarith only [hkc]
  intro hb
  have hb' := (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < edgeNeighborhoodMax G)).mp hb
  have hgm' : (G.totalDominationNumber : ℝ) * edgeNeighborhoodMax G ≤
      ((k : ℝ) + 7) * ((m : ℝ) * m) := by exact_mod_cast hgm
  have hcard' : (k : ℝ) * ((m : ℝ) * m) ≤ (minDegreeNeighborhood G).card := by
    exact_mod_cast hcard
  have hms : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hstrict : ((k : ℝ) + 7) * ((m : ℝ) * m) <
      c * ((minDegreeNeighborhood G).card : ℝ) := by
    calc
      _ < (c * k) * ((m : ℝ) * m) := mul_lt_mul_of_pos_right hks (mul_pos hms hms)
      _ = c * (k * ((m : ℝ) * m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard' (by linarith)
  exact (hstrict.trans_le (hb'.trans hgm')).false

/-- 常数 1 在二分图类中已经最优。 -/
theorem sharp_coefficient_bipartite (c : ℝ) : BipartiteValidCoefficient c ↔ c ≤ 1 := by
  constructor
  · intro h
    by_contra! hc
    obtain ⟨k, m, hk, hm, hconn, hbip, hbad⟩ := exists_bipartite_counterexample hc
    let _ : NeZero k := ⟨Nat.ne_of_gt hk⟩
    let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
    let _ : Nontrivial (Family.Vertex k m) :=
      ⟨⟨.inl (0, false, 0), .inr none, by simp⟩⟩
    exact hbad (h (Family.graph k m) hconn hbip)
  · intro hc V _ _ _ G _ hconn _
    exact coefficient_valid_of_le_one hc G hconn

/-- 通用不等式的最大实数系数是 1。 -/
theorem sharp_coefficient (c : ℝ) : ValidCoefficient c ↔ c ≤ 1 := by
  refine ⟨fun h => (sharp_coefficient_bipartite c).mp ?_, coefficient_valid_of_le_one⟩
  intro V _ _ _ G _ hconn _
  exact h G hconn

example : ValidCoefficient 1 := (sharp_coefficient 1).mpr le_rfl
example : ¬ BipartiteValidCoefficient 2 := by simp [sharp_coefficient_bipartite]

#print axioms sharp_coefficient
#print axioms sharp_coefficient_bipartite

end WOWII256
