module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic

@[expose] public section

/-!
本文件包含完全证明。两条最小阶定理或两题的锐性定理共用同一套定义。

总支配数定义沿用 Formal Conjectures 的 Apache-2.0 源码
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean，
提交 9097e2f90e66d2f6244209cb1c07f7120d17ec53。
-/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

/-- A set `D` is a total dominating set if every vertex is adjacent to a vertex
in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- An `n`-total dominating set is a total dominating set with `n` vertices. -/
@[mk_iff]
structure IsTotalNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : G.IsTotalDominating D
  card_eq : D.card = n

/-- The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

end SimpleGraph

namespace WOWII255

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 第 28 号定义中的边邻域。对端点的次序取两次不会改变最大值。 -/
def edgeNeighborhoodMax (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2)).sup
    (fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card)

/-- 第 64 号定义中的图中心的基数。 -/
noncomputable def centerCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.center.toFinset.card

/-- 第 255 题原不等式，使用实数除法。 -/
def Bound (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (2 * (centerCount G : ℝ)) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

end WOWII255

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax)

section

variable {V : Type*} [Fintype V]

/-- 最小度顶点集合的开邻域。 -/
def minDegreeNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => ∃ u, G.Adj v u ∧ ∀ w, G.degree u ≤ G.degree w)

/-- 在原题第 256 题中，分子为最小度顶点集合的开邻域的基数。 -/
def Bound (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] : Prop :=
  2 * ((minDegreeNeighborhood G).card : ℝ) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

end

end WOWII256

namespace WOWII255

open SimpleGraph

section LowerBound

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_le_edgeNeighborhoodMax {u v : V} (h : G.Adj u v) :
    G.degree u ≤ edgeNeighborhoodMax G := by
  have he : (u, v) ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  calc
    G.degree u = (G.neighborFinset u).card := (card_neighborFinset_eq_degree G u).symm
    _ ≤ (G.neighborFinset u ∪ G.neighborFinset v).card :=
      Finset.card_le_card Finset.subset_union_left
    _ ≤ edgeNeighborhoodMax G := Finset.le_sup
      (f := fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card) he

theorem edgeNeighborhoodMax_pos_of_edge {u v : V} (h : G.Adj u v) :
    0 < edgeNeighborhoodMax G := by
  have hv : v ∈ G.neighborFinset u := by rwa [mem_neighborFinset]
  have hp : 0 < G.degree u := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, hv⟩
  exact hp.trans_le (degree_le_edgeNeighborhoodMax G h)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem centerCount_le_order : centerCount G ≤ Fintype.card V := by
  classical
  unfold centerCount
  exact Finset.card_le_univ _

end LowerBound

end WOWII255

/-! 排除至多十个顶点的反例。 -/

namespace WOWII255

open SimpleGraph

section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem neighborhood_union_le {u v : V} (h : G.Adj u v) :
    (G.neighborFinset u ∪ G.neighborFinset v).card ≤ edgeNeighborhoodMax G := by
  have he : (u, v) ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  exact Finset.le_sup (f := fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card) he

theorem closed_neighborhood_subset {u v : V} (h : G.Adj u v) :
    insert u (G.neighborFinset u) ⊆ G.neighborFinset u ∪ G.neighborFinset v := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr h.symm)
  · exact Finset.mem_union_left _ hw

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem walk_stays {A : Finset V} {u v : V} (p : G.Walk u v)
    (h : ∀ ⦃x y⦄, x ∈ A → G.Adj x y → y ∈ A) (hu : u ∈ A) : v ∈ A := by
  induction p with
  | nil => exact hu
  | cons he _ ih => exact ih (h hu he)

theorem degree_add_two_le [Nontrivial V] (hG : G.Connected)
    (hM : edgeNeighborhoodMax G < Fintype.card V) (u : V) :
    G.degree u + 2 ≤ edgeNeighborhoodMax G := by
  by_contra h
  have hle : edgeNeighborhoodMax G ≤ G.degree u + 1 := by omega
  let A := insert u (G.neighborFinset u)
  have hu : u ∈ A := Finset.mem_insert_self _ _
  have hA : A.card = G.degree u + 1 := by
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self u),
      card_neighborFinset_eq_degree]
  have hclosed : ∀ ⦃x y⦄, x ∈ A → G.Adj x y → y ∈ A := by
    clear hG hM h
    intro x y hx hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr hxy)
    · exact
        have hux := (G.mem_neighborFinset _ _).mp hx
        have hcard : _ ≤ A.card := hA.symm ▸ (neighborhood_union_le G hux).trans hle
        have heq := Finset.eq_of_subset_of_card_le (closed_neighborhood_subset G hux) hcard
        show y ∈ insert u (G.neighborFinset u) from
          heq.symm ▸ Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr hxy)
  have hfull : A = Finset.univ := Finset.eq_univ_of_forall fun y =>
    let ⟨p⟩ := hG u y
    walk_stays G p hclosed hu
  obtain ⟨v, hv⟩ := hG.preconnected.exists_adj_of_nontrivial u
  have hm := (Finset.card_le_card (closed_neighborhood_subset G hv)).trans
    (neighborhood_union_le G hv)
  change A.card ≤ edgeNeighborhoodMax G at hm
  rw [hfull, Finset.card_univ] at hm
  exact hM.not_ge hm

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem minimum_set [Nontrivial V] (hG : G.Connected) :
    ∃ D : Finset V, G.IsTotalNDominatingSet G.totalDominationNumber D := by
  have h_exists : {n : ℕ | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, ⟨?_, Finset.card_univ⟩⟩
    intro u
    obtain ⟨v, hv⟩ := hG.preconnected.exists_adj_of_nontrivial u
    exact ⟨v, Finset.mem_univ _, hv⟩
  exact Nat.sInf_mem h_exists

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem totalDomination_ge_two [Nonempty V] {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) : 2 ≤ D.card := by
  obtain ⟨u, hu, _⟩ := hD (Classical.choice ‹Nonempty V›)
  obtain ⟨v, hv, huv⟩ := hD u
  by_contra h
  have hle : D.card ≤ 1 := by omega
  exact huv.ne ((Finset.card_le_one.mp hle) u hu v hv)

theorem order_le_domination_times_degree_bound {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) {d : ℕ} (hd : ∀ v, G.degree v ≤ d) :
    Fintype.card V ≤ D.card * d := by
  have hcov : D.biUnion (fun v => G.neighborFinset v) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hxv⟩ := hD x
    exact Finset.mem_biUnion.mpr ⟨v, hv, (G.mem_neighborFinset _ _).mpr hxv.symm⟩
  calc
    Fintype.card V = (D.biUnion fun v => G.neighborFinset v).card := by simp [hcov]
    _ ≤ ∑ v ∈ D, (G.neighborFinset v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ D, d := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [card_neighborFinset_eq_degree] using hd v
    _ = D.card * d := by simp

theorem order_le_max_of_domination_pair {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 2) :
    Fintype.card V ≤ edgeNeighborhoodMax G := by
  obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hcard
  have hab : G.Adj a b := by
    obtain ⟨v, hv, hav⟩ := hD a
    rcases (by simpa using hv : v = a ∨ v = b) with rfl | rfl
    · exact (hav.ne rfl).elim
    · exact hav
  have hcov : G.neighborFinset a ∪ G.neighborFinset b = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hxv⟩ := hD x
    rcases (by simpa using hv : v = a ∨ v = b) with rfl | rfl
    · exact Finset.mem_union_left _ ((G.mem_neighborFinset _ _).mpr hxv.symm)
    · exact Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr hxv.symm)
  simpa only [hcov, Finset.card_univ] using neighborhood_union_le G hab

/-- 边邻域不能覆盖全图时，两个顶点不足以总支配。 -/
theorem totalDomination_ge_three_of_max_lt_order [Nontrivial V]
    (hG : G.Connected) (hM : edgeNeighborhoodMax G < Fintype.card V) :
    3 ≤ G.totalDominationNumber := by
  obtain ⟨D, hD⟩ := minimum_set G hG
  have h₂ := totalDomination_ge_two G hD.isTotalDominating
  by_contra h
  have hcard : D.card = 2 := by have := hD.card_eq; omega
  exact hM.not_ge (order_le_max_of_domination_pair G hD.isTotalDominating hcard)

theorem order_add_three_le_of_path_dominates {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hac : a ≠ c)
    (hD : G.IsTotalDominating ({a, b, c} : Finset V)) :
    Fintype.card V + 3 ≤ 2 * edgeNeighborhoodMax G :=
  let X := G.neighborFinset a ∪ G.neighborFinset b
  let Y := G.neighborFinset b ∪ G.neighborFinset c
  have hU : X ∪ Y = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hxv⟩ := hD x
    rcases (by simpa using hv : v = a ∨ v = b ∨ v = c) with rfl | rfl | rfl <;>
      simp [X, Y, hxv.symm]
  have hs : ({a, b, c} : Finset V) ⊆ X ∩ Y := by
    intro x hx
    rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;>
      simp [X, Y, hab, hab.symm, hbc, hbc.symm]
  have hcard : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab.ne, hac, hbc.ne, rfl⟩
  have hI : 3 ≤ (X ∩ Y).card := hcard ▸ Finset.card_le_card hs
  have hX : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hab
  have hY : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hbc
  have hsum : Fintype.card V + (X ∩ Y).card = X.card + Y.card := by
    rw [← Finset.card_univ (α := V), ← hU]
    exact Finset.card_union_add_card_inter X Y
  by omega

omit [Fintype V] [DecidableRel G.Adj] in
theorem in_domination_triple {a b c : V}
    (hD : G.IsTotalDominating ({a, b, c} : Finset V)) {x : V} (hne : x = a) :
    G.Adj x b ∨ G.Adj x c := by
  obtain ⟨v, hv, hxv⟩ := hD x
  rcases (by simpa using hv : v = a ∨ v = b ∨ v = c) with rfl | rfl | rfl
  · exact (hxv.ne hne).elim
  · exact Or.inl hxv
  · exact Or.inr hxv

omit [Fintype V] [DecidableRel G.Adj] in
theorem domination_triple_path {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 3) :
    ∃ a b c, G.Adj a b ∧ G.Adj b c ∧ a ≠ c ∧ D = {a, b, c} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  by_cases h₁ : G.Adj a b
  · have hthird : G.Adj c a ∨ G.Adj c b := by
      apply in_domination_triple G ?_ rfl
      have heq : ({c, a, b} : Finset V) = {a, b, c} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rwa [heq]
    rcases hthird with hca | hcb
    · exact ⟨b, a, c, h₁.symm, hca.symm, hbc, Finset.insert_comm a b {c}⟩
    · exact ⟨a, b, c, h₁, hcb.symm, hac, rfl⟩
  · have ha := (in_domination_triple G hD rfl).resolve_left h₁
    have hswap : G.IsTotalDominating ({b, a, c} : Finset V) := by
      simpa only [Finset.insert_comm] using hD
    have hb := (in_domination_triple G hswap rfl).resolve_left (fun h => h₁ h.symm)
    exact ⟨a, c, b, ha, hb.symm, hab, congrArg (insert a) (Finset.pair_comm b c)⟩

theorem order_add_three_le_of_domination_triple {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 3) :
    Fintype.card V + 3 ≤ 2 * edgeNeighborhoodMax G := by
  obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := domination_triple_path G hD hcard
  exact order_add_three_le_of_path_dominates G hab hbc hac hD

/-- 十阶及以下满足更强的、以全体顶点数为分子的界。 -/
theorem order_times_two_le_domination_mul_max_of_card_le_ten [Nontrivial V]
    (hG : G.Connected) (hN : Fintype.card V ≤ 10) :
    2 * Fintype.card V ≤ G.totalDominationNumber * edgeNeighborhoodMax G := by
  obtain ⟨D, hD⟩ := minimum_set G hG
  have hg := totalDomination_ge_two G hD.isTotalDominating
  by_contra h
  have hlt : D.card * edgeNeighborhoodMax G < 2 * Fintype.card V := by
    rw [hD.card_eq]
    omega
  have hM : edgeNeighborhoodMax G < Fintype.card V := by
    by_contra hge
    have hm := Nat.mul_le_mul hg (Nat.le_of_not_gt hge)
    omega
  have hdeg (u : V) : G.degree u ≤ edgeNeighborhoodMax G - 2 := by
    have hu := degree_add_two_le G hG hM u
    omega
  have hprod := order_le_domination_times_degree_bound G hD.isTotalDominating hdeg
  have hm₂ : 2 ≤ edgeNeighborhoodMax G := by
    obtain ⟨u⟩ := hG.nonempty
    have hu := degree_add_two_le G hG hM u
    omega
  have hsum : D.card * (edgeNeighborhoodMax G - 2) + 2 * D.card =
      D.card * edgeNeighborhoodMax G := by
    calc
      _ = D.card * (edgeNeighborhoodMax G - 2 + 2) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hm₂]
  have hsmall : 2 * D.card < Fintype.card V := by omega
  have hcases : D.card = 2 ∨ D.card = 3 ∨ D.card = 4 := by omega
  rcases hcases with h₂ | h₃ | h₄
  · have hbig := order_le_max_of_domination_pair G hD.isTotalDominating h₂
    rw [h₂] at hlt
    omega
  · have hbig := order_add_three_le_of_domination_triple G hD.isTotalDominating h₃
    rw [h₃] at hlt
    omega
  · rw [h₄] at hlt hsmall hprod
    omega

theorem bound_of_card_le_ten [Nontrivial V] (hG : G.Connected)
    (hN : Fintype.card V ≤ 10) : Bound G := by
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨u, hu⟩ := hG.preconnected.exists_adj_of_nontrivial v
  have hM : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hu
  unfold Bound
  apply (div_le_iff₀ hM).mpr
  have h := (Nat.mul_le_mul_left 2 (centerCount_le_order G)).trans
    (order_times_two_le_domination_mul_max_of_card_le_ten G hG hN)
  exact_mod_cast h


end

end WOWII255

/-! 十一阶反例及其阶数的最小性。 -/

namespace WOWII255

open SimpleGraph

/-- 编号 0、1、2 分别为 a、b、c，编号 3 至 6 为 xᵢ，编号 7 至 10 为 yᵢ。 -/
def rowMask : Fin 11 → ℕ := ![122, 5, 1922, 241, 361, 601, 1081, 12, 20, 36, 68]

def adj11 (u v : Fin 11) : Prop :=
  u ≠ v ∧ (rowMask u).testBit v.val = true ∧ (rowMask v).testBit u.val = true

def graph11 : SimpleGraph (Fin 11) where
  Adj := adj11
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel graph11.Adj := by
  intro u v
  unfold graph11 adj11
  infer_instance

set_option maxHeartbeats 5000000 in
theorem routes : ∀ u v : Fin 11,
    u = v ∨ graph11.Adj u v ∨ ∃ z, graph11.Adj u z ∧ graph11.Adj z v := by
  decide

theorem short_walk11 (u v : Fin 11) : ∃ p : graph11.Walk u v, p.length ≤ 2 := by
  rcases routes u v with rfl | he | ⟨z, huz, hzv⟩
  · exact ⟨.nil, by simp⟩
  · exact ⟨.cons he .nil, by simp⟩
  · exact ⟨.cons huz (.cons hzv .nil), by simp⟩

theorem connected11 : graph11.Connected := by
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  exact ⟨(short_walk11 u v).choose⟩

theorem non_neighbor11 : ∀ u : Fin 11, ∃ v, u ≠ v ∧ ¬graph11.Adj u v := by decide

theorem eccentricity11 (u : Fin 11) : graph11.eccent u = 2 := by
  apply le_antisymm
  · apply (eccent_le_iff _ _).mpr
    intro v
    obtain ⟨p, hp⟩ := short_walk11 u v
    exact p.edist_le.trans (by exact_mod_cast hp)
  · obtain ⟨v, huv, hn⟩ := non_neighbor11 u
    have h : 1 < graph11.edist u v :=
      lt_of_not_ge fun hv => (edist_le_one_iff_adj_or_eq.mp hv).elim hn huv
    exact (Order.add_one_le_of_lt h).trans edist_le_eccent

theorem center_count11 : centerCount graph11 = 11 := by
  have heq : graph11.center = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro u
    obtain ⟨v, hv⟩ := graph11.exists_eccent_eq_radius
    exact (graph11.mem_center_iff u).mpr
      ((eccentricity11 u).trans ((eccentricity11 v).symm.trans hv))
  simp [centerCount, heq]

set_option maxHeartbeats 5000000 in
theorem edge_union11 : ∀ u v : Fin 11, graph11.Adj u v →
    (graph11.neighborFinset u ∪ graph11.neighborFinset v).card = 7 := by
  simp only [neighborFinset_eq_filter]
  decide

theorem edge_neighborhood_max11 : edgeNeighborhoodMax graph11 = 7 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    rintro ⟨u, v⟩ he
    exact (edge_union11 u v (Finset.mem_filter.mp he).2).le
  · have he : graph11.Adj 0 1 := by decide
    rw [← edge_union11 0 1 he]
    exact neighborhood_union_le graph11 he

def chosen11 : Finset (Fin 11) := {0, 1, 2}

theorem chosen_dominates11 : ∀ u : Fin 11, ∃ v ∈ chosen11, graph11.Adj u v := by decide

theorem total_domination11 : graph11.totalDominationNumber = 3 := by
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨chosen11, ⟨chosen_dominates11, by decide⟩⟩
  · apply totalDomination_ge_three_of_max_lt_order graph11 connected11
    rw [edge_neighborhood_max11, Fintype.card_fin]
    decide

theorem refutes_bound11 : ¬ Bound graph11 := by
  norm_num [Bound, center_count11, edge_neighborhood_max11, total_domination11]

/-- 阶数为 n 的连通简单图反例存在。 -/
def CounterexampleOrder (n : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (ha : DecidableRel G.Adj),
    letI := ha
    2 ≤ n ∧ G.Connected ∧ ¬ Bound G

/-- 原猜想的最小反例恰好有 11 个顶点。 -/
theorem smallest_counterexample_order : IsLeast {n | CounterexampleOrder n} 11 := by
  refine ⟨⟨graph11, inferInstance, by decide, connected11, refutes_bound11⟩, ?_⟩
  intro n hn
  obtain ⟨G, ha, h₂, hG, hbad⟩ := hn
  let _ : DecidableRel G.Adj := ha
  let _ : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simp only [Fintype.card_fin]; omega)
  by_contra h
  exact hbad (bound_of_card_le_ten G hG (by simp only [Fintype.card_fin]; omega))

example : CounterexampleOrder 11 := smallest_counterexample_order.1
example : ¬ CounterexampleOrder 10 := by
  intro h
  have : 11 ≤ 10 := smallest_counterexample_order.2 h
  omega


end WOWII255

/-! 第 256 题的十四阶见证。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax totalDomination_ge_three_of_max_lt_order)

/-- 0、1、2 是总支配路径。3 至 13 是一个十一点环，0 连 4 至 8，
1 连 3，2 连 9 至 13。 -/
def rowMask : Fin 14 → ℕ := ![498, 13, 15874, 8210, 41, 81, 161, 321, 641, 1284, 2564, 5124, 10244, 4108]

def adj14 (u v : Fin 14) : Prop :=
  u ≠ v ∧ (rowMask u).testBit v.val = true ∧ (rowMask v).testBit u.val = true

def graph14 : SimpleGraph (Fin 14) where
  Adj := adj14
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel graph14.Adj := by
  intro u v
  unfold graph14 adj14
  infer_instance

theorem hubRoute : ∀ v : Fin 14,
    v = 1 ∨ graph14.Adj v 1 ∨ ∃ u, graph14.Adj v u ∧ graph14.Adj u 1 := by decide

theorem connected14 : graph14.Connected := by
  have reach (v : Fin 14) : graph14.Reachable v 1 := by
    rcases hubRoute v with h | h | ⟨u, hv, hz⟩
    · subst v
      exact ⟨.nil⟩
    · exact ⟨h.toWalk⟩
    · exact ⟨.cons hv hz.toWalk⟩
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  exact (reach u).trans (reach v).symm

def degreeValue14 (u : Fin 14) : ℕ :=
  if u = 0 ∨ u = 2 then 6 else 3

theorem degree14 : ∀ u : Fin 14, graph14.degree u = degreeValue14 u := by
  simp only [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  decide

theorem has_min_degree_neighbor14 : ∀ x : Fin 14,
    ∃ u, graph14.Adj x u ∧ degreeValue14 u = 3 := by decide

theorem min_degree_neighborhood_count14 : (minDegreeNeighborhood graph14).card = 14 := by
  have h : minDegreeNeighborhood graph14 = Finset.univ := by
    ext v
    simp only [minDegreeNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    obtain ⟨u, hvu, hu⟩ := has_min_degree_neighbor14 v
    refine ⟨u, hvu, fun w => ?_⟩
    rw [degree14, degree14, hu]
    unfold degreeValue14
    split_ifs <;> decide
  rw [h, Finset.card_univ, Fintype.card_fin]

set_option maxHeartbeats 5000000 in
theorem edgeUnionLe : ∀ u v : Fin 14, graph14.Adj u v →
    (graph14.neighborFinset u ∪ graph14.neighborFinset v).card ≤ 9 := by
  simp only [neighborFinset_eq_filter]
  decide

theorem edge_neighborhood_max14 : edgeNeighborhoodMax graph14 = 9 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    rintro ⟨u, v⟩ he
    exact edgeUnionLe u v (Finset.mem_filter.mp he).2
  · have he : graph14.Adj 0 1 := by decide
    have hcard : (graph14.neighborFinset 0 ∪ graph14.neighborFinset 1).card = 9 := by
      simp only [neighborFinset_eq_filter]
      decide
    rw [← hcard]
    exact WOWII255.neighborhood_union_le graph14 he

def chosen14 : Finset (Fin 14) := {0, 1, 2}

theorem total_domination14 : graph14.totalDominationNumber = 3 := by
  apply le_antisymm
  · apply Nat.sInf_le
    have hd : ∀ v : Fin 14, ∃ u ∈ chosen14, graph14.Adj v u := by decide
    exact ⟨chosen14, ⟨hd, by decide⟩⟩
  · exact totalDomination_ge_three_of_max_lt_order graph14 connected14
      (by simp [edge_neighborhood_max14])

theorem refutes_bound14 : ¬ Bound graph14 := by
  norm_num [Bound, min_degree_neighborhood_count14, total_domination14, edge_neighborhood_max14]


end WOWII256

/-! 第 256 题最小反例的阶数。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax neighborhood_union_le degree_add_two_le minimum_set
  totalDomination_ge_two order_le_domination_times_degree_bound order_le_max_of_domination_pair
  edgeNeighborhoodMax_pos_of_edge domination_triple_path order_add_three_le_of_domination_triple)

section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev edgeBall (a b : V) := G.neighborFinset a ∪ G.neighborFinset b

omit [DecidableEq V] in
theorem covered_by {D X : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (h : ∀ d ∈ D, G.neighborFinset d ⊆ X) : X = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨v, hv, hxv⟩ := hD x
  exact h v hv ((G.mem_neighborFinset _ _).mpr hxv.symm)

theorem path_in_inter {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) :
    ({a, b, c} : Finset V) ⊆ edgeBall G a b ∩ edgeBall G b c := by
  intro x hx
  rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;>
    simp [edgeBall, hab, hab.symm, hbc, hbc.symm]

theorem target_card_lt_order_of_triple {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 3)
    (hM : 5 ≤ edgeNeighborhoodMax G)
    (heq : Fintype.card V + 3 = 2 * edgeNeighborhoodMax G) :
    (minDegreeNeighborhood G).card < Fintype.card V := by
  obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := domination_triple_path G hD hcard
  exact
    let X := edgeBall G a b
    let Y := edgeBall G b c
    have hun := covered_by G hD (X := X ∪ Y) (by
      intro x hx z hz
      rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;>
        simp only [X, Y, edgeBall, Finset.mem_union, hz, true_or, or_true])
    have hsub : ({a, b, c} : Finset V) ⊆ X ∩ Y := path_in_inter G hab hbc
    have hi : 3 ≤ (X ∩ Y).card := hcard ▸ Finset.card_le_card hsub
    have hx : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hab
    have hy : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hbc
    have hs : Fintype.card V + (X ∩ Y).card = X.card + Y.card := by
      rw [← Finset.card_univ (α := V), ← hun]
      exact Finset.card_union_add_card_inter X Y
    have hcut : X ∩ Y = {a, b, c} :=
      (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; omega)).symm
    have hnb : G.neighborFinset b = {a, c} := by
      clear hD hcard hM heq hac hun hsub hi hx hy hs
      ext u
      constructor
      · intro hu
        have hh : u ∈ X ∩ Y :=
          Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hu, Finset.mem_union_left _ hu⟩
        rw [hcut] at hh
        rcases (by simpa using hh : u = a ∨ u = b ∨ u = c) with ha | hb | hc
        · simp [ha]
        · exact (G.notMem_neighborFinset_self b (hb ▸ hu)).elim
        · simp [hc]
      · intro hu
        rcases (by simpa using hu : u = a ∨ u = c) with rfl | rfl <;>
          simp [hab.symm, hbc]
    have hdb : G.degree b = 2 := by
      rw [← card_neighborFinset_eq_degree, hnb]
      simp [hac]
    have hxa : X.card ≤ G.degree a + G.degree b := by
      dsimp [X, edgeBall]
      simpa only [card_neighborFinset_eq_degree] using
        Finset.card_union_le (G.neighborFinset a) (G.neighborFinset b)
    have hyc : Y.card ≤ G.degree b + G.degree c := by
      dsimp [Y, edgeBall]
      simpa only [card_neighborFinset_eq_degree] using
        Finset.card_union_le (G.neighborFinset b) (G.neighborFinset c)
    have hmiss : b ∉ minDegreeNeighborhood G := by
      clear hD hcard hab hbc hac hun hsub hcut
      simp only [minDegreeNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨u, hbu, hmin⟩
      have hmem := (G.mem_neighborFinset _ _).mpr hbu
      rw [hnb] at hmem
      rcases (by simpa using hmem : u = a ∨ u = c) with rfl | rfl <;>
        have hb := hmin b <;> omega
    have hproper : minDegreeNeighborhood G ⊂ Finset.univ := by
      apply Finset.ssubset_univ_iff.mpr
      intro h
      exact hmiss (by rw [h]; exact Finset.mem_univ b)
    show _ from by simpa using Finset.card_lt_card hproper

def HasMatchingPair (D : Finset V) : Prop :=
  ∃ a ∈ D, ∃ b ∈ D, ∃ c ∈ D, ∃ d ∈ D, G.Adj a b ∧ G.Adj c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

omit [Fintype V] [DecidableRel G.Adj] in
theorem star_of_no_matching_pair {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : 3 ≤ D.card)
    (hn : ¬ HasMatchingPair G D) :
    ∃ r ∈ D, ∀ u ∈ D, u ≠ r → G.Adj r u :=
  have touch {a b c d : V} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
      (hab : G.Adj a b) (hcd : G.Adj c d) : a = c ∨ a = d ∨ b = c ∨ b = d := by
    by_contra! h
    exact hn ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  let ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  let ⟨b, hb, hab⟩ := hD a
  have hlt : ({a, b} : Finset V).card < D.card := by
    simp [hab.ne]; omega
  let ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hca : c ≠ a := fun h => hcn (by simp [h])
  have hcb : c ≠ b := fun h => hcn (by simp [h])
  let ⟨d, hd, hcd⟩ := hD c
  have hcenter : ∃ r ∈ D, ∃ s ∈ D, ∃ t ∈ D, G.Adj r s ∧ G.Adj r t ∧ s ≠ t := by
    rcases touch ha hb hc hd hab hcd with h | h | h | h
    · exact (hca h.symm).elim
    · subst d
      exact ⟨a, ha, b, hb, c, hc, hab, hcd.symm, hcb.symm⟩
    · exact (hcb h.symm).elim
    · subst d
      exact ⟨b, hb, a, ha, c, hc, hab.symm, hcd.symm, hca.symm⟩
  let ⟨r, hr, s, hs, t, ht, hrs, hrt, hst⟩ := hcenter
  ⟨r, hr, fun u hu hur => by
    clear hcard hn a ha b hb hab hlt c hc hcn d hd hcd hca hcb
    by_contra hnru
    obtain ⟨v, hv, huv⟩ := hD u
    exact
      have hus : u ≠ s := fun h => hnru (h ▸ hrs)
      have hut : u ≠ t := fun h => hnru (h ▸ hrt)
      have hvr : v ≠ r := fun h => hnru (h ▸ huv.symm)
      have h1 := touch hr hs hu hv hrs huv
      have h2 := touch hr ht hu hv hrt huv
      by grind⟩

theorem ball_contains_star {D : Finset V} {r x : V}
    (hstar : ∀ u ∈ D, u ≠ r → G.Adj r u) (hrx : G.Adj r x) :
    D ⊆ edgeBall G r x := by
  intro u hu
  by_cases h : u = r
  · subst u
    simp [edgeBall, hrx.symm]
  · simp [edgeBall, hstar u hu h]

theorem four_star_bound {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (hcard : D.card = 4) {r : V} (hr : r ∈ D)
    (hstar : ∀ u ∈ D, u ≠ r → G.Adj r u) :
    Fintype.card V + 8 ≤ 3 * edgeNeighborhoodMax G :=
  have hleaves : (D.erase r).card = 3 := by rw [Finset.card_erase_of_mem hr, hcard]
  let ⟨a, b, c, _, _, _, he⟩ := Finset.card_eq_three.mp hleaves
  have hD' : D = {r, a, b, c} := by
    rw [← Finset.insert_erase hr, he]
  have ha := hstar a (by simp [hD']) (by
    have h : a ∈ D.erase r := by rw [he]; simp
    exact (Finset.mem_erase.mp h).1)
  have hb := hstar b (by simp [hD']) (by
    have h : b ∈ D.erase r := by rw [he]; simp
    exact (Finset.mem_erase.mp h).1)
  have hc := hstar c (by simp [hD']) (by
    have h : c ∈ D.erase r := by rw [he]; simp
    exact (Finset.mem_erase.mp h).1)
  let X := edgeBall G r a
  let Y := edgeBall G r b
  let Z := edgeBall G r c
  have hfull := covered_by G hD (X := (X ∪ Y) ∪ Z) (by
    intro x hx y hy
    rw [hD'] at hx
    rcases (by simpa using hx : x = r ∨ x = a ∨ x = b ∨ x = c) with
      rfl | rfl | rfl | rfl <;>
      simp only [X, Y, Z, edgeBall, Finset.mem_union, hy, true_or, or_true])
  have hX : D ⊆ X := ball_contains_star G hstar ha
  have hY : D ⊆ Y := ball_contains_star G hstar hb
  have hZ : D ⊆ Z := ball_contains_star G hstar hc
  have hi : D ⊆ X ∩ Y := fun x hx => Finset.mem_inter.mpr ⟨hX hx, hY hx⟩
  have hi' : D ⊆ (X ∪ Y) ∩ Z :=
    fun x hx => Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hX hx), hZ hx⟩
  have hci : 4 ≤ (X ∩ Y).card := hcard ▸ Finset.card_le_card hi
  have hci' : 4 ≤ ((X ∪ Y) ∩ Z).card := hcard ▸ Finset.card_le_card hi'
  have hx : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G ha
  have hy : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hb
  have hz : Z.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hc
  have hp := Finset.card_union_add_card_inter X Y
  have hq : Fintype.card V + ((X ∪ Y) ∩ Z).card = (X ∪ Y).card + Z.card := by
    rw [← Finset.card_univ (α := V), ← hfull]
    exact Finset.card_union_add_card_inter (X ∪ Y) Z
  by omega

theorem four_matching_bound {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (hcard : D.card = 4) (hm : HasMatchingPair G D) :
    Fintype.card V ≤ 2 * edgeNeighborhoodMax G :=
  let ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hac, had, hbc, hbd⟩ := hm
  have hsub : ({a, b, c, d} : Finset V) ⊆ D := by
    simp [ha, hb, hc, hd, Finset.insert_subset_iff]
  have hD' := (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp [hab.ne,
    hcd.ne, hac, had, hbc, hbd])).symm
  let X := edgeBall G a b
  let Y := edgeBall G c d
  have hfull := covered_by G hD (X := X ∪ Y) (by
    clear hD hcard ha hb hc hd hab hcd hac had hbc hbd hsub
    intro x hx y hy
    rw [hD'] at hx
    rcases (by simpa using hx : x = a ∨ x = b ∨ x = c ∨ x = d) with
      rfl | rfl | rfl | rfl <;>
      simp only [X, Y, edgeBall, Finset.mem_union, hy, true_or, or_true])
  have hs : Fintype.card V ≤ X.card + Y.card :=
    by simpa only [hfull, Finset.card_univ] using Finset.card_union_le X Y
  have hxy : X.card + Y.card ≤ edgeNeighborhoodMax G + edgeNeighborhoodMax G :=
    Nat.add_le_add (neighborhood_union_le G hab) (neighborhood_union_le G hcd)
  (hs.trans hxy).trans_eq (two_mul _).symm

theorem five_matching_bound {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (hcard : D.card = 5) (hm : HasMatchingPair G D) :
    Fintype.card V + 3 ≤ 3 * edgeNeighborhoodMax G :=
  let ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hac, had, hbc, hbd⟩ := hm
  have hfour : ({a, b, c, d} : Finset V).card = 4 := by simp [hab.ne, hcd.ne,
    hac, had, hbc, hbd]
  let ⟨e, he, hen⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a, b, c, d} : Finset V).card < D.card by omega)
  let ⟨f, hf, hef⟩ := hD e
  have he' : e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by simpa using hen
  have hsub : ({e, a, b, c, d} : Finset V) ⊆ D := by
    simp [ha, hb, hc, hd, he, Finset.insert_subset_iff]
  have hD' := (Finset.eq_of_subset_of_card_le hsub (by rw [hcard,
    Finset.card_insert_of_notMem hen, hfour])).symm
  let X := edgeBall G a b
  let Y := edgeBall G c d
  let Z := edgeBall G e f
  have hfull := covered_by G hD (X := (X ∪ Y) ∪ Z) (by
    clear hD hcard ha hb hc hd hab hcd hac had hbc hbd hfour he hen hf hef he' hsub
    intro x hx y hy
    rw [hD'] at hx
    rcases (by simpa using hx : x = e ∨ x = a ∨ x = b ∨ x = c ∨ x = d) with
      rfl | rfl | rfl | rfl | rfl <;>
      simp only [X, Y, Z, edgeBall, Finset.mem_union, hy, true_or, or_true])
  have hoverlap {u v : V} (huv : G.Adj u v) (hev : G.Adj e v) (hue : u ≠ e)
      (hxy : edgeBall G u v ⊆ X ∪ Y) : 3 ≤ ((X ∪ Y) ∩ edgeBall G e v).card := by
    clear hD hcard ha hb hc hd hfour he hen hf he' hsub hD' hfull
    have hp := path_in_inter G huv hev.symm
    have hcard₃ : ({u, v, e} : Finset V).card = 3 := by simp [huv.ne, hev.ne.symm, hue]
    rw [← hcard₃]
    apply Finset.card_le_card
    intro x hx
    have h := Finset.mem_inter.mp (hp hx)
    exact Finset.mem_inter.mpr ⟨hxy h.1, by simpa [edgeBall, Finset.union_comm] using h.2⟩
  have hi : 3 ≤ ((X ∪ Y) ∩ Z).card := by
    clear hD hcard ha hb hc hd hac had hbc hbd hfour he hen hsub hfull
    rw [hD'] at hf
    rcases (by simpa using hf : f = e ∨ f = a ∨ f = b ∨ f = c ∨ f = d) with
      rfl | rfl | rfl | rfl | rfl
    · exact (hef.ne rfl).elim
    · exact hoverlap hab.symm hef he'.2.1.symm (by
        simpa only [X, edgeBall, Finset.union_comm (G.neighborFinset b) (G.neighborFinset f)]
          using (Finset.subset_union_left : X ⊆ X ∪ Y))
    · exact hoverlap hab hef he'.1.symm Finset.subset_union_left
    · exact hoverlap hcd.symm hef he'.2.2.2.symm (by
        simpa only [Y, edgeBall, Finset.union_comm (G.neighborFinset d) (G.neighborFinset f)]
          using (Finset.subset_union_right : Y ⊆ X ∪ Y))
    · exact hoverlap hcd hef he'.2.2.1.symm Finset.subset_union_right
  have hx : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hab
  have hy : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hcd
  have hz : Z.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hef
  have hxy := Finset.card_union_le X Y
  have hs : Fintype.card V + ((X ∪ Y) ∩ Z).card = (X ∪ Y).card + Z.card := by
    rw [← Finset.card_univ (α := V), ← hfull]
    exact Finset.card_union_add_card_inter (X ∪ Y) Z
  by omega

omit [DecidableEq V] in
theorem target_card_le_order : (minDegreeNeighborhood G).card ≤ Fintype.card V :=
  Finset.card_le_univ _

/-- 至多十三点的图满足第 256 题原不等式。 -/
theorem bound_of_card_le_thirteen [Nontrivial V] (hG : G.Connected)
    (hN : Fintype.card V ≤ 13) : Bound G := by
  have hMpos : (0 : ℝ) < edgeNeighborhoodMax G := by
    obtain ⟨v⟩ := hG.nonempty
    obtain ⟨u, hu⟩ := hG.preconnected.exists_adj_of_nontrivial v
    exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hu
  unfold Bound
  apply (div_le_iff₀ hMpos).mpr
  by_contra! hbad
  obtain ⟨D, hD⟩ := minimum_set G hG
  have hbad' : D.card * edgeNeighborhoodMax G < 2 * (minDegreeNeighborhood G).card := by
    rw [hD.card_eq]
    exact_mod_cast hbad
  clear hMpos hbad
  have hd := hD.isTotalDominating
  clear hD
  have hlt := hbad'.trans_le (Nat.mul_le_mul_left 2 (target_card_le_order G))
  have hm : edgeNeighborhoodMax G < Fintype.card V :=
    lt_of_not_ge fun h =>
      (Nat.not_lt_of_ge (Nat.mul_le_mul (totalDomination_ge_two G hd) h)) hlt
  have hdeg (i : V) : G.degree i ≤ edgeNeighborhoodMax G - 2 :=
    Nat.le_sub_of_add_le (degree_add_two_le G hG hm i)
  have hprod := order_le_domination_times_degree_bound G hd hdeg
  have hsmall : 2 * D.card < Fintype.card V := by
    obtain ⟨v⟩ := hG.nonempty
    have hm₂ : 2 ≤ edgeNeighborhoodMax G :=
      (Nat.le_add_left 2 (G.degree v)).trans (degree_add_two_le G hG hm v)
    have hsum : D.card * (edgeNeighborhoodMax G - 2) + 2 * D.card =
        D.card * edgeNeighborhoodMax G := by
      rw [Nat.mul_comm 2, ← Nat.mul_add, Nat.sub_add_cancel hm₂]
    omega
  have hcases : D.card = 2 ∨ D.card = 3 ∨ D.card = 4 ∨ D.card = 5 ∨ D.card = 6 :=
    by have := totalDomination_ge_two G hd; omega
  rcases hcases with h₂ | h₃ | h₄ | h₅ | h₆
  · exact hm.not_ge (order_le_max_of_domination_pair G hd h₂)
  · clear hprod hsmall hdeg hm hG
    have hb := order_add_three_le_of_domination_triple G hd h₃
    rw [h₃] at hlt hbad'
    have hcases' : (Fintype.card V = 11 ∧ edgeNeighborhoodMax G = 7) ∨
        (Fintype.card V = 13 ∧ edgeNeighborhoodMax G = 8) := by omega
    have hs := target_card_lt_order_of_triple G hd h₃ (by omega) (by omega)
    omega
  · clear hprod hdeg hm hG hbad'
    rw [h₄] at hlt hsmall
    exact
      (em (HasMatchingPair G D)).elim
        (fun hmatch => by have := four_matching_bound G hd h₄ hmatch; omega)
        (fun hmatch =>
          let ⟨r, hr, hstar⟩ := star_of_no_matching_pair G hd (by omega) hmatch
          by have := four_star_bound G hd h₄ hr hstar; omega)
  · clear hm hG hbad'
    rw [h₅] at hlt hprod hsmall
    have hm₅ : edgeNeighborhoodMax G = 5 := by omega
    exact
      (em (HasMatchingPair G D)).elim
        (fun hmatch => by have := five_matching_bound G hd h₅ hmatch; omega)
        (fun hmatch =>
          let ⟨r, hr, hstar⟩ := star_of_no_matching_pair G hd (by omega) hmatch
          have hsub : D.erase r ⊆ G.neighborFinset r :=
            fun x hx => (G.mem_neighborFinset _ _).mpr
              (hstar x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1)
          have hh : D.card - 1 ≤ G.degree r := by
            rw [← Finset.card_erase_of_mem hr, ← card_neighborFinset_eq_degree]
            exact Finset.card_le_card hsub
          have := hdeg r
          by omega)
  · rw [h₆] at hlt hprod hsmall
    omega

end

/-- 原猜想在给定阶数的有限连通简单图上存在反例。 -/
def CounterexampleOrder (n : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (ha : DecidableRel G.Adj),
    letI := ha
    2 ≤ n ∧ G.Connected ∧ ¬ Bound G

/-- 最小反例恰有十四个顶点。 -/
theorem smallest_counterexample_order : IsLeast {n | CounterexampleOrder n} 14 := by
  refine ⟨⟨graph14, inferInstance, by decide, connected14, refutes_bound14⟩, ?_⟩
  rintro n ⟨G, ha, h₂, hG, hbad⟩
  let _ : DecidableRel G.Adj := ha
  let _ : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simp only [Fintype.card_fin]; omega)
  by_contra! h
  exact hbad (bound_of_card_le_thirteen G hG (by simp only [Fintype.card_fin]; omega))

example : CounterexampleOrder 14 := smallest_counterexample_order.1

example : ¬ CounterexampleOrder 13 := by
  intro h
  have : 14 ≤ 13 := smallest_counterexample_order.2 h
  omega


end WOWII256

#print axioms WOWII255.smallest_counterexample_order
#print axioms WOWII256.smallest_counterexample_order
