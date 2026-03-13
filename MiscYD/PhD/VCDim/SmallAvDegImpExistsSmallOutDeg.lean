import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card

open scoped Finset

namespace SimpleGraph
variable {V : Type*} [Finite V] {G : SimpleGraph V} {d : ℕ}

/-- A bipartite simple graph whose induced subgraphs all have average degree at most `2 * d` can be
oriented in such a way that all edges have outdegree at most `d`. -/
lemma exists_orientation_of_average_degree_le (hGcolorable : G.Colorable 2)
    (hGdeg : ∀ s : Finset V, (G.induce s).edgeSet.ncard ≤ d * #s) :
    ∃ r : V → V → Prop, Std.Irrefl r ∧ Std.Asymm r := sorry

end SimpleGraph
