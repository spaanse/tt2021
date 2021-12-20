import algebra
import algebra.algebra.basic
import data.nat.basic
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

instance sj_has_mul.to_has_scalar (α : Type*) [sj_has_mul α] : sj_has_scalar α α := { 
  sj_smul := λ (a: α) (b: α), a * b 
}

-- 2.2 
def apply_n {α : Type*} [add_comm_monoid α] : ℕ → (α → α → α) → α → α
| 0     f x := 0
| (k+1) f x := f (apply_n k f x) x

instance sj_repeated_add.to_has_scalar (α : Type*) [add_comm_monoid α] [module ℤ α] : sj_has_scalar ℕ α := {
  sj_smul := λ (n: ℕ) (x: α), apply_n n has_add.add x
}

-- 3

variables R M N I J α : Type*

instance sj_function.has_scalar [has_mul α] : has_scalar α (I → α) := {
  smul := λ r v, (λ i, r * v i)
}

instance sj_matrix.has_scalar [has_mul α] : has_scalar α (I → J → α) := {
  smul := λ r v, (λ i j, r * v i j)
}

instance sj_matrix.has_scalar' [has_mul α] [has_scalar α (J → α)] : has_scalar α (I → (J → α)) := {
  smul := λ r v, (λ i j, r * v i j)
}

instance sj_function.has_scalar' [has_scalar α M] : has_scalar α (I → M) := {
  smul := λ r v, (λ i, r • v i)
}

instance sj_pi.has_scalar (f : I → Type*) [Π i : I, has_scalar α (f i)] : has_scalar α (Π i : I, f i) := {
  smul := λ r v, (λ i, r • v i)
}

-- 3.1
instance addmap.has_scalar [has_scalar R N] [add_zero_class M] [add_zero_class N] : has_scalar R (M →+ N) := {
  smul := λ r f, {
    to_fun := λ i, r • f i,
    map_zero' := by {
      simp, 
      sorry,
    },
    map_add' := by {
      simp, 
      sorry,
    },
  }
}

-- algebra.module.hom
instance addmap.distrib_mul_action [monoid R] [add_monoid M] [add_comm_monoid N] [distrib_mul_action R N] : distrib_mul_action R (M →+ N) := {
  smul := λr f, {
    to_fun := λ i, r • f i,
    map_zero' := by simp,
    map_add' := λ x y, by simp [smul_add],
  },
  one_smul := λ f, by simp,
  mul_smul := λ r s f, by simp [mul_smul],
  smul_add := λ r f g, add_monoid_hom.ext (λ x, by simp [smul_add]),
  smul_zero := λ r,add_monoid_hom.ext (λ x, by simp [smul_zero]),
}


section linmap_has_scalar

variables [add_comm_monoid M] [add_comm_monoid N]
instance linmap.has_scalar₁ 
[semiring R] [module R M] [module R N] [has_scalar α N] : 
has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by {
      intros m₁ m₂, 
      rw f.map_add,
      sorry,
    },
    map_smul' := by {
      intros r m,
      rw f.map_smul,
      simp,
      sorry,
    },
  }
}

instance linmap.has_scalar₂ [semiring R] [module R M] [module R N] [monoid α] [distrib_mul_action α N] : has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by {
      intros m₁ m₂,
      rw f.map_add,
      rw smul_add,
    },
    map_smul' := by {
      intros r m,
      rw f.map_smul,
      rw ring_hom.id_apply,
      sorry,
    },
  }
}

instance linmap.has_scalar₃ [comm_semiring R] [module R M] [module R N] : has_scalar R (M →ₗ[R] N) := {
  smul := λ r f, {
    to_fun := λ m, r • f m,
    map_add' := by simp,
    map_smul' := by {
      intros s m,
      rw f.map_smul,
      rw ring_hom.id_apply,
      rw ← mul_smul,
      rw ← mul_smul,
      rw mul_comm,
    },
  }
}

instance linmap.has_scalar₄ [semiring R] [comm_semiring α] [module R M] [module R N] [algebra α R] [module α N] [is_scalar_tower α R N] : has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by simp,
    map_smul' := by {
      intros r m, simp,
      rw ← smul_assoc,
      rw algebra.smul_def', simp,
      rw ← algebra_map,
      rw algebra.commutes,
      rw mul_smul,
      congr,
      rw algebra_map_smul, 
    },
  }
}

instance linmap.has_scalar₅ [semiring R] [module R M] [module R N] [monoid α] [distrib_mul_action α N] [smul_comm_class α R N] : has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by simp,
    map_smul' := by {
      intros r m,
      rw f.map_smul,
      rw ring_hom.id_apply,
      rw smul_comm,
    },
  }
}
end linmap_has_scalar


section algrebras

end algrebras

end scalar