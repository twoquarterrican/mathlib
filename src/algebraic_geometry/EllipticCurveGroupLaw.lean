import algebraic_geometry.EllipticCurve
import tactic

namespace EllipticCurve

variables {K : Type*} [field K] (E : EllipticCurve K)

inductive points (E : EllipticCurve K)
| zero : points
| some (x y : K) (h : y^2+E.a1*x*y+E.a3*y=x^3+E.a2*x^2+E.a4*x+E.a6) : points

open points

variable {E}

def neg : points E → points E
| zero := zero
| (some x y h) := some x (-E.a3 - E.a1 * x - y) begin
  rw ← h,
  ring,
end

theorem neg_neg : ∀ P : points E, neg (neg P) = P
| zero := rfl
| (some x y h) := by simp [neg]

variable [decidable_eq K]

protected def add : points E → points E → points E
| zero           zero           := zero
| zero           (some x y h)   := some x y h
| (some x y h)   zero           := some x y h
| (some a b hab) (some c d hcd) :=
if h : (a = c) ∧ b + d + E.a3 + E.a1 * a = 0 then zero else
sorry

instance : has_add (points E) := ⟨EllipticCurve.add⟩

lemma add_assoc : ∀ {P Q R : points E}, P + Q + R = P + (Q + R)
| zero           zero           zero           := rfl
| (some a b hab) zero           zero           := rfl
| zero           (some c d hcd) zero           := rfl
| zero           zero           (some e f hef) := rfl
| (some a b hab) (some c d hcd) zero           := sorry
| (some a b hab) zero           (some e f hef) := rfl
| zero           (some c d hcd) (some e f hef) := sorry
| one more left

end EllipticCurve
