import Note198.SelectingRectification
import Note198.EnvelopingProjective

namespace Note198.SelectingRectification
noncomputable section
open CategoryTheory OAI.LittleFinitistic
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (E : SelectionEncoding.Encoding k R) (S : EndomorphismSelection.Data k R)

/-- The actual fixed selecting complex is projective over the enveloping
algebra in each degree. Its source is chosen before any Y. -/
theorem bimodule_enveloping_projective : ∀ n, Projective ((bimodule E S).X n) := by
  exact EnvelopingProjective.total_enveloping_projective
    (ConcreteQuadraticDiagram.quadratic E.relations)
    (D₀ E S) (D₁ E S) (D₂ E S) (f E S) (g E S) (relations E S)
    (SourceVerdier.vertex_idem E.relations 0)
    (SourceVerdier.vertex_idem E.relations 1)
    (SourceVerdier.vertex_idem E.relations 2)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S).D₀)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S).D₁)
    (UnderlyingRepresentatives.projective E.relations (fixedData E S).D₂)

end
end Note198.SelectingRectification
