open lean
open tactic
open interactive

@[intro] lemma option_bind_some_back {α β : Type} :
  forall (o1 : option α) (o2 : α → option β) v v',
    o1 = some v →
    o2 v = some v' →
    o1 >>= o2 = some v' :=
begin
  intros,
  rw a,
  simp [bind, has_bind.bind, option.bind],
  rw a_1,
end

lemma option_bind_some {α β : Type} :
  forall (o1 : option α) (o2 : α → option β) v,
    o1 >>= o2 = some v →
    exists v', o1 = some v' ∧
      o2 v' = some v :=
begin
  intros, destruct o1 ; intros,
  unfold bind at *, subst a_1,
  dsimp [option.bind] at *,
  cases a,
  subst a_1,
  unfold bind at *,
  dsimp [option.bind] at *,
  constructor,
  split, reflexivity,
  assumption,
end

meta def simp_option (hyp_name : parse lean.parser.ident) : tactic unit :=
do h ← get_local hyp_name,
   ty ← tactic.infer_type h,
   (a :: b :: o1 :: o2 :: v :: _) ← tactic.match_expr
     ``(fun (a b : Type) (o1 : option a) (o2 : a → option b) (v : b), has_bind.bind o1 o2 = some v) ty | tactic.failed,
   n ← get_unused_name `o,
   prf ← to_expr ``(option_bind_some %%o1 %%o2 %%v %%h),
   tactic.note n none prf,
   vn ← get_unused_name `v,
   ex ← get_local n,
   cases ex [vn, n],
   conj ← get_local n,
   r ← get_unused_name `right,
   l ← get_unused_name `left,
   cases conj [l, r],
   get_local hyp_name >>= clear,
   try (get_local l >>= dsimp_hyp),
   try (get_local r >>= dsimp_hyp),
   return ()
