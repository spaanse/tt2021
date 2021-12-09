import algebra.group

#print has_scalar



instance int.has_scalar : has_scalar ℕ ℕ := {
  smul := λ n m, n * m,
}

section scalar

-- 1.1 Typeclasses
class sj_has_mul (G : Type*) :=
(sj_mul : G → G → G)

infix * := sj_has_mul.sj_mul

class sj_semigroup (G : Type*) extends sj_has_mul G :=
(sj_mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

lemma sj_mul_assoc₂ {G : Type*} [sj_semigroup G] (a b c d : G) : a * (b * (c * d)) = ((a * b) * c) * d :=
by {
  rw [sj_semigroup.sj_mul_assoc],
  rw [sj_semigroup.sj_mul_assoc],
}

structure sj_opposite (α : Type*) := (x : α)
instance (T : Type*) [sj_semigroup T] : sj_semigroup (sj_opposite T) :=
{ sj_mul := λ a b, ⟨b.x * a.x⟩,
  sj_mul_assoc := λ a b c, congr_arg sj_opposite.mk (sj_semigroup.sj_mul_assoc c.x b.x a.x).symm
}

-- 1.2 the has_scalar typeclass
class sj_has_scalar (M : Type*) (α : Type*) := (sj_smul : M → α → α)
infixr ` • `:73 := sj_has_scalar.sj_smul
class sj_mul_action (M : Type*) (α : Type*) [monoid M] extends sj_has_scalar M α :=
(sj_one_smul : ∀ a : α, (1 : M) • a = a)
(sj_mul_smul : ∀ (x y : M) (a : α), (x * y) • a = x • y • a)

-- 2.1 left multiplication

instance sj_has_mul.to_has_scalar (α : Type*) [sj_has_mul α] : sj_has_scalar α α := { sj_smul := (*) }

-- 2.2 



end scalar