import WOWII255PairFamily

/-! 第 255 题中通用系数恰为所有不超过 1 的实数。 -/

namespace WOWII255

open SimpleGraph

/-- 用参数 `c` 代替原猜想中的常数 2。 -/
def CoefficientBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  (c * (centerCount G : ℝ)) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

theorem coefficient_two_is_original {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : CoefficientBound G 2 ↔ Bound G := Iff.rfl

/-- 量化所有有限连通简单图。非平凡性使分母有意义。 -/
def ValidCoefficient (c : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → CoefficientBound G c

theorem coefficient_valid_of_le_one {c : ℝ} (hc : c ≤ 1) : ValidCoefficient c := by
  intro V _ _ _ G _ hG
  have hadj := hG.preconnected.exists_adj_of_nontrivial
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨v, hv⟩ := hadj u
  have hM : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hv
  unfold CoefficientBound
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ 1 * (centerCount G : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by
      rw [one_mul]
      exact_mod_cast (centerCount_le_order G).trans (order_le_totalDomination_mul_max G hadj)

private theorem numerator_le (n extra : ℕ) (hn : 2 ≤ n) :
    (n + 2) * (2 * (n * extra) + extra) ≤ (2 * n + 6) * (n * extra) := by
  calc
    _ = (2 * n * n + 5 * n + 2) * extra := by ring
    _ ≤ (2 * n * n + 6 * n) * extra := Nat.mul_le_mul_right extra (by omega)
    _ = _ := by ring

/-- 对每个实数 `c > 1` 给出解析构造的反例。 -/
theorem exists_pair_counterexample {c : ℝ} (hc : 1 < c) :
    ∃ k copies : ℕ, 0 < copies ∧ (PairFamily.graph k copies).Connected ∧
      0 < edgeNeighborhoodMax (PairFamily.graph k copies) ∧
      ¬ CoefficientBound (PairFamily.graph k copies) c := by
  obtain ⟨k, hk⟩ := exists_nat_gt (3 / (c - 1))
  let n := k + 2
  let extra := 2 + (2 * n) * (2 * n)
  let copies := n * extra
  let G := PairFamily.graph k copies
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hcopies : 0 < copies := by dsimp [copies, n, extra]; positivity
  let _ : NeZero copies := ⟨Nat.ne_of_gt hcopies⟩
  have hM : 0 < edgeNeighborhoodMax G := PairFamily.max_edge_neighborhood_pos k copies
  refine ⟨k, copies, hcopies, PairFamily.connected k copies, hM, ?_⟩
  have hg : G.totalDominationNumber ≤ n + 2 := PairFamily.domination_le k copies
  have hm : edgeNeighborhoodMax G ≤ 2 * copies + extra := by
    simpa only [G, n, extra, Nat.add_assoc] using PairFamily.max_edge_neighborhood_le k copies
  have hz : 2 * n * copies ≤ centerCount G := by
    change 2 * n * copies ≤ centerCount (PairFamily.graph k copies)
    rw [PairFamily.center_count]
    change 2 * n * copies ≤ (2 * n) * (2 * n) + (2 + 2 * n * copies)
    omega
  have hmuld : G.totalDominationNumber * edgeNeighborhoodMax G ≤ (2 * n + 6) * copies :=
    (Nat.mul_le_mul hg hm).trans (numerator_le n extra hn)
  have hk' : 3 < (k : ℝ) * (c - 1) := (div_lt_iff₀ (sub_pos.mpr hc)).mp hk
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Nat.le_add_right k 2)
  have hnc : 3 < (n : ℝ) * (c - 1) :=
    hk'.trans_le (mul_le_mul_of_nonneg_right hkn (sub_nonneg.mpr hc.le))
  have hcompare : 2 * (n : ℝ) + 6 < c * (2 * (n : ℝ)) := by nlinarith only [hnc]
  have hcpos : 0 ≤ c := by linarith
  show ¬ CoefficientBound G c
  intro h
  unfold CoefficientBound at h
  have hcond := (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < edgeNeighborhoodMax G)).mp h
  have hmuldr : (G.totalDominationNumber : ℝ) * edgeNeighborhoodMax G ≤
      (2 * (n : ℝ) + 6) * copies := by exact_mod_cast hmuld
  have hzreal : 2 * (n : ℝ) * copies ≤ centerCount G := by exact_mod_cast hz
  have hstrict : (2 * (n : ℝ) + 6) * copies < c * (centerCount G : ℝ) := by
    calc
      _ < (c * (2 * (n : ℝ))) * copies :=
        mul_lt_mul_of_pos_right hcompare (by exact_mod_cast hcopies)
      _ = c * (2 * (n : ℝ) * copies) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hzreal hcpos
  exact (hstrict.trans_le (hcond.trans hmuldr)).false

/-- 必要与充分条件。通用不等式的最大实数系数为 1。 -/
theorem sharp_coefficient (c : ℝ) : ValidCoefficient c ↔ c ≤ 1 := by
  refine ⟨?_, coefficient_valid_of_le_one⟩
  intro h
  by_contra! hc
  obtain ⟨k, m, _, hconn, _, hbad⟩ := exists_pair_counterexample hc
  have : Nontrivial (PairFamily.Vertex k m) :=
    ⟨⟨.inr (.inl false), .inr (.inl true), by simp⟩⟩
  exact hbad (h (PairFamily.graph k m) hconn)

-- 基例检查顶点计数和端点。集成检查排除原猜想使用的系数 2。
example : centerCount (PairFamily.graph 0 1) = 22 := by
  rw [PairFamily.center_count]

example : ValidCoefficient 1 := (sharp_coefficient 1).mpr le_rfl

example : ¬ ValidCoefficient 2 := by
  intro h
  have := (sharp_coefficient 2).mp h
  norm_num at this

#print axioms coefficient_valid_of_le_one
#print axioms exists_pair_counterexample
#print axioms sharp_coefficient

end WOWII255
