import PEqualNP.MetaComplexity.L104
import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_756_aux

private def arm (i j : Fin 6) : Bool :=
  (i == 0 && (j == 1 || j == 2 || j == 3 || j == 4)) ||
  (i == 1 && j == 5)

private abbrev spider : SimpleGraph (Fin 6) where
  Adj i j := (arm i j || arm j i) = true
  symm := ⟨fun _ _ => by simp [Bool.or_comm]⟩
  loopless := ⟨by decide⟩

private theorem edge_count : spider.edgeFinset.card = 5 := by decide

private theorem forest : spider.IsAcyclic := by
  apply SimpleGraph.IsTree.isAcyclic
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  constructor
  · apply spider.connected_iff_exists_forall_reachable.mpr
    refine ⟨0, ?_⟩
    intro w
    fin_cases w
    · exact SimpleGraph.Reachable.rfl
    · exact (show spider.Adj 0 1 by decide).reachable
    · exact (show spider.Adj 0 2 by decide).reachable
    · exact (show spider.Adj 0 3 by decide).reachable
    · exact (show spider.Adj 0 4 by decide).reachable
    · exact (show spider.Adj 0 1 by decide).reachable.trans
        (show spider.Adj 1 5 by decide).reachable
  · rw [Nat.card_eq_fintype_card, ← spider.edgeFinset_card, edge_count,
        Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem cover_lower (T : Finset (Fin 6))
    (h : ∀ i j : Fin 6, spider.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  have ha := h 0 2 (by decide)
  have hb := h 1 5 (by decide)
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    exact Finset.one_lt_card.mpr ⟨_, ha, _, hb, by decide⟩

private theorem edge_fn :
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6,
      spider.Adj i j ∧ x i = true ∧ x j = true)) =
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) ||
      (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) := by
  funext x
  decide +revert

theorem lower (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) ||
      (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) s) : 6 ≤ s := by
  rw [← edge_fn] at h
  have hb := PEqualNP.MetaComplexity.L104 6 2 s spider forest
    ⟨0, 1, by decide⟩ cover_lower h
  rw [edge_count] at hb
  omega

end PEqualNP.Outside.L_meta_756_aux

namespace PEqualNP.Outside.L_meta_756_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wires 6 to 8 combine the four neighbors of vertex 0.
private def spiderCircuit : Circuit where
  gates := [⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩,
            ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 10]⟩]
  output := 11

private theorem spiderCircuit_eval (a b c d e f : Bool) :
    spiderCircuit.eval [a, b, c, d, e, f] =
      ((a && b) || (a && c) || (a && d) || (a && e) || (b && f)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

theorem upper_bound (s : ℕ) (hs : 6 ≤ s) :
    HasCircuitSize 6 (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
        (x 0 && x 4) || (x 1 && x 5)) s := by
  refine ⟨spiderCircuit, ?_, hs, ?_⟩
  · simp [FanInTwo, spiderCircuit]
  · intro x
    exact spiderCircuit_eval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

end PEqualNP.Outside.L_meta_756_aux

theorem PEqualNP.Outside.L_meta_756 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  exact ⟨PEqualNP.Outside.L_meta_756_aux.lower s, PEqualNP.Outside.L_meta_756_aux.upper_bound s⟩
