import algebra
import algebra.algebra.basic
import data.nat.basic
#print has_scalar

instance int.has_scalar : has_scalar ℕ ℕ := {
  smul := λ n m, n * m,
}

section scalar

-- 1.1 Typeclasses
class has_mulₜₜ (G : Type*) :=
(mul : G → G → G)

infix * := has_mulₜₜ.mul

class semigroupₜₜ (G : Type*) extends has_mulₜₜ G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

lemma mul_assoc₂ {G : Type*} [semigroupₜₜ G] (a b c d : G) : a * (b * (c * d)) = ((a * b) * c) * d :=
by {
  rw [semigroupₜₜ.mul_assoc],
  rw [semigroupₜₜ.mul_assoc],
}

structure opposite (α : Type*) := (x : α)
instance (T : Type*) [semigroupₜₜ T] : semigroupₜₜ (opposite T) :=
{ mul := λ a b, ⟨b.x * a.x⟩,
  mul_assoc := λ a b c, congr_arg opposite.mk (semigroupₜₜ.mul_assoc c.x b.x a.x).symm
}

-- 1.2 the has_scalar typeclass
class has_scalarₜₜ (M : Type*) (α : Type*) := (smul : M → α → α)

infixr ` • `:73 := has_scalarₜₜ.smul

class mul_actionₜₜ (M : Type*) (α : Type*) [monoid M] extends has_scalar M α :=
(one_smul : ∀ a : α, (1 : M) • a = a)
(mul_smul : ∀ (x y : M) (a : α), (x * y) • a = x • y • a)

-- 2.1 left multiplication

instance has_mul.to_has_scalarₜₜ (α : Type*) [has_mulₜₜ α] : has_scalarₜₜ α α := {
  smul := λ (a: α) (b: α), a * b
}

-- 2.2 
def apply_n {α : Type*} [add_comm_monoid α] : ℕ → (α → α → α) → α → α
| 0     f x := 0
| (k+1) f x := f (apply_n k f x) x

instance repeated_add.to_has_scalarₜₜ (α : Type*) [add_comm_monoid α] [module ℤ α] : has_scalarₜₜ ℕ α := {
  smul := λ (n: ℕ) (x: α), apply_n n has_add.add x
}

-- 3

variables R M N I J α : Type*

instance function.has_scalarₜₜ [has_mul α] : has_scalar α (I → α) := {
  smul := λ r v, (λ i, r * v i)
}

instance matrix.has_scalarₜₜ [has_mul α] : has_scalar α (I → J → α) := {
  smul := λ r v, (λ i j, r * v i j)
}

instance matrix.has_scalar'ₜₜ [has_mul α] [has_scalar α (J → α)] : has_scalar α (I → (J → α)) := {
  smul := λ r v, (λ i j, r * v i j)
}

instance function.has_scalar'ₜₜ [has_scalar α M] : has_scalar α (I → M) := {
  smul := λ r v, (λ i, r • v i)
}

instance pi.has_scalarₜₜ (f : I → Type*) [Π i : I, has_scalar α (f i)] : has_scalar α (Π i : I, f i) := {
  smul := λ r v, (λ i, r • v i)
}

-- 3.1
instance add_monoid_hom.has_scalar [has_scalar R N] [add_zero_class M] [add_zero_class N] : has_scalar R (M →+ N) := {
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
instance add_monoid_hom.distrib_mul_actionₜₜ [monoid R] [add_monoid M] [add_comm_monoid N] [distrib_mul_action R N] : distrib_mul_action R (M →+ N) := {
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

variables [semiring R]
variables [add_comm_monoid M] [add_comm_monoid N]
variables [module R N][module R M]
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
      intros r m, simp,
      sorry,
    }
  }
}

instance linmap.has_scalar₂ [monoid α] [distrib_mul_action α N] : has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by {
      intros m₁ m₂,
      rw f.map_add,
      rw smul_add,
    },
    map_smul' := by {
      intros r m, simp,
      sorry,
    }
  }
}

instance linmap.has_scalar₃ [comm_semiring α] [module α N] [module α M] : has_scalar α (M →ₗ[α] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by simp,
    map_smul' := by {
      intros s m, simp,
      rw ← mul_smul,
      rw ← mul_smul,
      rw mul_comm,
    }
  }
}

instance linmap.has_scalar₄ [comm_semiring α] [module α N] [algebra α R] [is_scalar_tower α R N] : has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by simp,
    map_smul' := by {
      intros r m, simp,
      rw ← smul_assoc,
      rw algebra.smul_def,
      rw algebra.commutes,
      rw mul_smul,
      rw algebra_map_smul,
    }
  }
}

instance linmap.has_scalar₅ [monoid α] [distrib_mul_action α N] [smul_comm_class α R N] : has_scalar α (M →ₗ[R] N) := {
  smul := λ a f, {
    to_fun := λ m, a • f m,
    map_add' := by simp,
    map_smul' := by {
      intros r m, simp,
      rw smul_comm,
    }
  }
}
end linmap_has_scalar


section algrebras

end algrebras

end scalar
