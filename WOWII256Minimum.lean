import WOWII256Small

/-! 第 256 题最小反例的阶数。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax neighborhood_union_le degree_add_two_le minimum_set
  totalDomination_ge_two order_le_domination_times_degree_bound order_le_max_of_domination_pair
  edgeNeighborhoodMax_pos_of_edge domination_triple_path order_add_three_le_of_domination_triple)

section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private abbrev edgeBall (a b : V) := G.neighborFinset a ∪ G.neighborFinset b

omit [DecidableEq V] in
private theorem covered_by {D X : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (h : ∀ d ∈ D, G.neighborFinset d ⊆ X) : X = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨v, hv, hxv⟩ := hD x
  exact h v hv ((G.mem_neighborFinset _ _).mpr hxv.symm)

private theorem path_in_inter {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) :
    ({a, b, c} : Finset V) ⊆ edgeBall G a b ∩ edgeBall G b c := by
  intro x hx
  rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;>
    simp [edgeBall, hab, hab.symm, hbc, hbc.symm]

private theorem target_card_lt_order_of_triple {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 3)
    (hM : 5 ≤ edgeNeighborhoodMax G)
    (heq : Fintype.card V + 3 = 2 * edgeNeighborhoodMax G) :
    (minDegreeNeighborhood G).card < Fintype.card V := by
  obtain ⟨a, b, c, hab, hbc, hac, rfl⟩ := domination_triple_path G hD hcard
  let X := edgeBall G a b
  let Y := edgeBall G b c
  have hun := covered_by G hD (X := X ∪ Y) (by
    intro x hx z hz
    rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hz))
  have hsub : ({a, b, c} : Finset V) ⊆ X ∩ Y := path_in_inter G hab hbc
  have hi := Finset.card_le_card hsub
  rw [hcard] at hi
  have hx : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hab
  have hy : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hbc
  have hs := Finset.card_union_add_card_inter X Y
  rw [hun, Finset.card_univ] at hs
  have hcut : X ∩ Y = {a, b, c} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; omega)).symm
  have hnb : G.neighborFinset b = {a, c} := by
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
  simpa using Finset.card_lt_card hproper

private def HasMatchingPair (D : Finset V) : Prop :=
  ∃ a ∈ D, ∃ b ∈ D, ∃ c ∈ D, ∃ d ∈ D, G.Adj a b ∧ G.Adj c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d

omit [Fintype V] [DecidableRel G.Adj] in
private theorem star_of_no_matching_pair {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : 3 ≤ D.card)
    (hn : ¬ HasMatchingPair G D) :
    ∃ r ∈ D, ∀ u ∈ D, u ≠ r → G.Adj r u := by
  have touch {a b c d : V} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hd : d ∈ D)
      (hab : G.Adj a b) (hcd : G.Adj c d) : a = c ∨ a = d ∨ b = c ∨ b = d := by
    by_contra! h
    exact hn ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  obtain ⟨b, hb, hab⟩ := hD a
  have hlt : ({a, b} : Finset V).card < D.card := by
    simp [hab.ne]; omega
  obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hca : c ≠ a := fun h => hcn (by simp [h])
  have hcb : c ≠ b := fun h => hcn (by simp [h])
  obtain ⟨d, hd, hcd⟩ := hD c
  have hcenter : ∃ r ∈ D, ∃ s ∈ D, ∃ t ∈ D, G.Adj r s ∧ G.Adj r t ∧ s ≠ t := by
    rcases touch ha hb hc hd hab hcd with h | h | h | h
    · exact (hca h.symm).elim
    · subst d
      exact ⟨a, ha, b, hb, c, hc, hab, hcd.symm, hcb.symm⟩
    · exact (hcb h.symm).elim
    · subst d
      exact ⟨b, hb, a, ha, c, hc, hab.symm, hcd.symm, hca.symm⟩
  obtain ⟨r, hr, s, hs, t, ht, hrs, hrt, hst⟩ := hcenter
  refine ⟨r, hr, fun u hu hur => ?_⟩
  by_contra hnru
  obtain ⟨v, hv, huv⟩ := hD u
  have hus : u ≠ s := fun h => hnru (h ▸ hrs)
  have hut : u ≠ t := fun h => hnru (h ▸ hrt)
  have hvr : v ≠ r := fun h => hnru (h ▸ huv.symm)
  have h1 := touch hr hs hu hv hrs huv
  have h2 := touch hr ht hu hv hrt huv
  grind

private theorem ball_contains_star {D : Finset V} {r x : V}
    (hstar : ∀ u ∈ D, u ≠ r → G.Adj r u) (hrx : G.Adj r x) :
    D ⊆ edgeBall G r x := by
  intro u hu
  by_cases h : u = r
  · subst u
    simp [edgeBall, hrx.symm]
  · simp [edgeBall, hstar u hu h]

private theorem four_star_bound {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (hcard : D.card = 4) {r : V} (hr : r ∈ D)
    (hstar : ∀ u ∈ D, u ≠ r → G.Adj r u) :
    Fintype.card V + 8 ≤ 3 * edgeNeighborhoodMax G := by
  have hleaves : (D.erase r).card = 3 := by rw [Finset.card_erase_of_mem hr, hcard]
  obtain ⟨a, b, c, _, _, _, he⟩ := Finset.card_eq_three.mp hleaves
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
      rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hy))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hy))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hy))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hy))
  have hX : D ⊆ X := ball_contains_star G hstar ha
  have hY : D ⊆ Y := ball_contains_star G hstar hb
  have hZ : D ⊆ Z := ball_contains_star G hstar hc
  have hi : D ⊆ X ∩ Y := fun x hx => Finset.mem_inter.mpr ⟨hX hx, hY hx⟩
  have hi' : D ⊆ (X ∪ Y) ∩ Z :=
    fun x hx => Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (hX hx), hZ hx⟩
  have hci := Finset.card_le_card hi
  have hci' := Finset.card_le_card hi'
  rw [hcard] at hci hci'
  have hx : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G ha
  have hy : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hb
  have hz : Z.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hc
  have hp := Finset.card_union_add_card_inter X Y
  have hq := Finset.card_union_add_card_inter (X ∪ Y) Z
  rw [hfull, Finset.card_univ] at hq
  omega

private theorem four_matching_bound {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (hcard : D.card = 4) (hm : HasMatchingPair G D) :
    Fintype.card V ≤ 2 * edgeNeighborhoodMax G := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hac, had, hbc, hbd⟩ := hm
  have hsub : ({a, b, c, d} : Finset V) ⊆ D := by
    simp [ha, hb, hc, hd, Finset.insert_subset_iff]
  have hD' := (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp [hab.ne,
    hcd.ne, hac, had, hbc, hbd])).symm
  let X := edgeBall G a b
  let Y := edgeBall G c d
  have hfull := covered_by G hD (X := X ∪ Y) (by
    intro x hx y hy
    rw [hD'] at hx
    rcases (by simpa using hx : x = a ∨ x = b ∨ x = c ∨ x = d) with
      rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hy)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hy)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hy)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hy))
  have hs := Finset.card_union_le X Y
  rw [hfull, Finset.card_univ] at hs
  have hxy : X.card + Y.card ≤ edgeNeighborhoodMax G + edgeNeighborhoodMax G :=
    Nat.add_le_add (neighborhood_union_le G hab) (neighborhood_union_le G hcd)
  simpa only [two_mul] using hs.trans hxy

private theorem five_matching_bound {D : Finset V} (hD : G.IsTotalDominating (D : Set V))
    (hcard : D.card = 5) (hm : HasMatchingPair G D) :
    Fintype.card V + 3 ≤ 3 * edgeNeighborhoodMax G := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hab, hcd, hac, had, hbc, hbd⟩ := hm
  have hfour : ({a, b, c, d} : Finset V).card = 4 := by simp [hab.ne, hcd.ne,
    hac, had, hbc, hbd]
  obtain ⟨e, he, hen⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({a, b, c, d} : Finset V).card < D.card by omega)
  obtain ⟨f, hf, hef⟩ := hD e
  have he' : e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d := by simpa using hen
  have hsub : ({e, a, b, c, d} : Finset V) ⊆ D := by
    simp [ha, hb, hc, hd, he, Finset.insert_subset_iff]
  have hD' := (Finset.eq_of_subset_of_card_le hsub (by rw [hcard,
    Finset.card_insert_of_notMem hen, hfour])).symm
  let X := edgeBall G a b
  let Y := edgeBall G c d
  let Z := edgeBall G e f
  have hfull := covered_by G hD (X := (X ∪ Y) ∪ Z) (by
    intro x hx y hy
    rw [hD'] at hx
    rcases (by simpa using hx : x = e ∨ x = a ∨ x = b ∨ x = c ∨ x = d) with
      rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hy)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hy))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hy))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _ hy))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hy)))
  have hoverlap {u v : V} (huv : G.Adj u v) (hev : G.Adj e v) (hue : u ≠ e)
      (hxy : edgeBall G u v ⊆ X ∪ Y) : 3 ≤ ((X ∪ Y) ∩ edgeBall G e v).card := by
    have hp := path_in_inter G huv hev.symm
    have hcard₃ : ({u, v, e} : Finset V).card = 3 := by simp [huv.ne, hev.ne.symm, hue]
    rw [← hcard₃]
    apply Finset.card_le_card
    intro x hx
    have h := Finset.mem_inter.mp (hp hx)
    exact Finset.mem_inter.mpr ⟨hxy h.1, by simpa [edgeBall, Finset.union_comm] using h.2⟩
  have hi : 3 ≤ ((X ∪ Y) ∩ Z).card := by
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
  have hs := Finset.card_union_add_card_inter (X ∪ Y) Z
  rw [hfull, Finset.card_univ] at hs
  omega

omit [DecidableEq V] in
private theorem target_card_le_order : (minDegreeNeighborhood G).card ≤ Fintype.card V :=
  Finset.card_le_univ _

/-- 至多十三点的图满足第 256 题原不等式。 -/
theorem bound_of_card_le_thirteen [Nontrivial V] (hG : G.Connected)
    (hN : Fintype.card V ≤ 13) : Bound G := by
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨u, hu⟩ := hG.preconnected.exists_adj_of_nontrivial v
  have hMpos : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hu
  unfold Bound
  apply (div_le_iff₀ hMpos).mpr
  obtain ⟨D, hD⟩ := minimum_set G hG
  have hdc := hD.card_eq
  have hd := hD.isTotalDominating
  by_contra! hbad
  have hbad' : D.card * edgeNeighborhoodMax G < 2 * (minDegreeNeighborhood G).card := by
    rw [hdc]
    exact_mod_cast hbad
  have ht := target_card_le_order G
  have hlt : D.card * edgeNeighborhoodMax G < 2 * Fintype.card V := by omega
  have hg := totalDomination_ge_two G hd
  have hm : edgeNeighborhoodMax G < Fintype.card V := by
    by_contra! h
    have := Nat.mul_le_mul hg h
    omega
  have hm₂ : 2 ≤ edgeNeighborhoodMax G := by have := degree_add_two_le G hG hm v; omega
  have hdeg (i : V) : G.degree i ≤ edgeNeighborhoodMax G - 2 := by
    have := degree_add_two_le G hG hm i
    omega
  have hprod := order_le_domination_times_degree_bound G hd hdeg
  have hsum : D.card * (edgeNeighborhoodMax G - 2) + 2 * D.card =
      D.card * edgeNeighborhoodMax G := by
    calc
      _ = D.card * (edgeNeighborhoodMax G - 2 + 2) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hm₂]
  have hsmall : 2 * D.card < Fintype.card V := by omega
  have hcases : D.card = 2 ∨ D.card = 3 ∨ D.card = 4 ∨ D.card = 5 ∨ D.card = 6 := by omega
  rcases hcases with h₂ | h₃ | h₄ | h₅ | h₆
  · exact hm.not_ge (order_le_max_of_domination_pair G hd h₂)
  · have hb := order_add_three_le_of_domination_triple G hd h₃
    rw [h₃] at hlt hbad'
    have hcases' : (Fintype.card V = 11 ∧ edgeNeighborhoodMax G = 7) ∨
        (Fintype.card V = 13 ∧ edgeNeighborhoodMax G = 8) := by omega
    have hs := target_card_lt_order_of_triple G hd h₃ (by omega) (by omega)
    omega
  · rw [h₄] at hlt hsmall
    by_cases hmatch : HasMatchingPair G D
    · have := four_matching_bound G hd h₄ hmatch
      omega
    · obtain ⟨r, hr, hstar⟩ := star_of_no_matching_pair G hd (by omega) hmatch
      have := four_star_bound G hd h₄ hr hstar
      omega
  · rw [h₅] at hlt hprod hsmall
    have hm₅ : edgeNeighborhoodMax G = 5 := by omega
    by_cases hmatch : HasMatchingPair G D
    · have := five_matching_bound G hd h₅ hmatch
      omega
    · obtain ⟨r, hr, hstar⟩ := star_of_no_matching_pair G hd (by omega) hmatch
      have hsub : D.erase r ⊆ G.neighborFinset r := by
        intro x hx
        obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
        exact (G.mem_neighborFinset _ _).mpr (hstar x hmem hne)
      have hh := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hr, h₅, card_neighborFinset_eq_degree] at hh
      have := hdeg r
      omega
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

#print axioms bound_of_card_le_thirteen
#print axioms smallest_counterexample_order

end WOWII256
