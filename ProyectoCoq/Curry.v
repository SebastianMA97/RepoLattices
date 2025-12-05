From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.
From ProyectoCoq Require Import Dualidad.
From ProyectoCoq Require Import Ltac_Dual.

Notation ρ := (reflexT _).
Notation τ := (transT _).
Notation σ := (antisymT _).

Lemma dobl (A : Prop) :  A <-> A /\ A.
Proof.
split. by [].
move=> [h1 h2]; by [].
Qed.

Lemma ΛK {T : lattice} (z : T) : forall a b : T ,  (a ⊓ b) ≤ a.
Proof.
move=> a b.
move: (ρ (a ⊓ b)).
by rewrite -(MH (a ⊓ b) a b) => /proj1.
Qed.

Lemma ΛK' {T : lattice} (z : T) : forall a b : T , (a ⊓ b) ≤ b.
Proof.
move=> a b.
move: (ρ (a ⊓ b)).
by rewrite -(MH (a ⊓ b) a b) => /proj2.
Qed.

Lemma ΛS {T : lattice} (z : T) : forall a b c : T , ((c ≤ a /\ c ≤ b) -> c ≤ (a ⊓ b)).
Proof.
move=> a b c.
by move: (MH c a b) => /proj1.
Qed.

(*       Teorema 1           *)

Theorem ΛW {T : lattice} (z : T) : forall a: T, a ≤ (a ⊓ a).
Proof.
move=> a.
move: (ρ a)=> H.
move: (conj H H).
by move=> /(ΛS z).
Qed.

Theorem ΛC {T : lattice} (z : T) : forall a b : T, a ⊓ b ≤ (b ⊓ a).
Proof.
move=> a b.
move: (ΛK' z a b)=> H0.
move: (ΛK z a b)=> H1.
move: (conj H0 H1).
by move=> /(ΛS z).
Qed.

Theorem ΛB {T : lattice} (z : T) : forall a b c : T, a ≤ b -> c ⊓ a ≤ (c ⊓ b).
Proof.
move=> a b c H.
move: (ΛK z c a)=> H0.
move: (τ _ _ _ (ΛK' z c a) H)=> H1.
move: (conj H0 H1).
by move=> /(ΛS z).
Qed.

Theorem ΛB' {T : lattice} (z : T) : forall a b c : T, a ≤ b -> a ⊓ c ≤ (b ⊓ c).
Proof.
move=> a b c H.
move: (ΛB z a b c H).
move: (ΛC z a c)=> H0.
move: (ΛC z c b)=> H1.
move=> /(τ _ _ _ H0)=> H2.
by move: (τ _ _ _ H2 H1).
Qed.

(*       Teorema 2           *)

From ProyectoCoq Require Import CurryThm2.

(*       Teorema 3           *)

Lemma semil {T : lattice} (z : T) :  forall a b : T, a = b -> a ≤ b.
Proof.
move=> a b H.
rewrite H.
by move: (ρ b).
Qed.

Lemma semir {T : lattice} (z : T) :  forall a b : T, a = b -> b ≤ a.
Proof.
move=> a b H.
rewrite H.
by move: (ρ b).
Qed.

Theorem ΛL1 {T : lattice} (z : T) : forall a : T, a ⊓ a = a.
Proof.
move=> a.
apply σ; last first.
  by move: (ΛW z a).
(* Prueba por reflexión *)
reflectS_goal z [:: a] meetT.
rewrite /evalS_f.
apply leq_impl_Leq.
move=> /=.
by left.
Qed.

Theorem ΛL2 {T : lattice} (z : T) : forall a b : T, a ⊓ b = b ⊓ a.
Proof.
move=> a b.
(* Prueba por reflexión *)
reflectS_goal z [:: a ; b] meetT.
rewrite /evalS_f.
apply σ.
  apply leq_impl_Leq.
  move=> /=.
  split.
    by right.
  by left.
apply leq_impl_Leq.
move=> /=.
split.
  by right.
by left.
Qed.

Theorem ΛL3 {T : lattice} (z : T) : forall a b c : T, a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c.
Proof.
move=> a b c.
(* Prueba por reflexión *)
reflectS_goal z [:: a ; b ; c] meetT.
rewrite /evalS_f.
apply σ.
  apply leq_impl_Leq.
  move=> /=.
  split.
    split.
      by left.
    by right; left.
  by right; right.
apply leq_impl_Leq.
move=> /=.
split.
  by left; left.
split.
  by left; right.
by right.
Qed.

Theorem ΛC3 {T : lattice} (z : T) : forall a b : T, a ≤ b <-> a = (a ⊓ b).
Proof.
move=> a b.
split => H.
  move: (conj (ρ a) H).
  move=> /(ΛS z)=> H0.
  by move: ((σ a (a ⊓ b)) H0 (ΛK z a b)).
by move: ((τ _ _ _) ((semil z) _ _ H) (ΛK' z a b)).
Qed.

(* 2._ Lattices en general *)

Lemma VK {T : lattice} (z : T) : forall a b : T ,  a ≤ (a ⊔ b).
Proof.
move=> a b.
(* Por dualidad *)
reflect_goal z [:: a ; b] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛK L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

Lemma VK' {T : lattice} (z : T) : forall a b : T , b ≤ (a ⊔ b).
Proof.
move=> a b.
(* Por dualidad *)
reflect_goal z [:: a ; b] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛK' L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

Lemma VS {T : lattice} (z : T) : forall a b c : T , ((a ≤ c /\ b ≤ c) -> (a ⊔ b) ≤ c ).
Proof.
move=> a b c.
(* Por dualidad *)
reflect_goal z [:: a ; b ; c] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛS L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1))
(eval L0 z0 env0 (Var 2)) ).
Qed.

(* Teorema 4 Dualidad *)

(* Teorema 5 *)

Theorem VL1 {T : lattice} (z : T) : forall a : T, a ⊔ a = a.
Proof.
move=> a.
(* Por dualidad *)
reflect_goal z [:: a] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛL1 L0 z0) (eval L0 z0 env0 (Var 0)) ).
Qed.

Theorem VL2 {T : lattice} (z : T) : forall a b : T, a ⊔ b = b ⊔ a.
Proof.
move=> a b.
(* Por dualidad *)
reflect_goal z [:: a ; b] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛL2 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

Theorem VL3 {T : lattice} (z : T) : forall a b c : T, a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c.
Proof.
move=> a b c.
(* Por dualidad *)
reflect_goal z [:: a ; b ; c] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛL3 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1))
 (eval L0 z0 env0 (Var 2)) ).
Qed.

Theorem VC3 {T : lattice} (z : T) : forall a b : T, a ≤ b <-> b = (b ⊔ a).
Proof.
rewrite /iff => a b.
(* Por dualidad *)
reflect_goal z [:: a ; b] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛC3 L0 z0) (eval L0 z0 env0 (Var 1)) (eval L0 z0 env0 (Var 0)) ).
Qed.

Theorem ΛL4 {T : lattice} (z : T) : forall a b : T, a ⊓ (a ⊔ b) = a.
Proof.
move=> a b.
apply σ.
  by move: (ΛK z a (a ⊔ b)).
move: (ρ a) (VK z a b)=> H0 H1.
by move: (((ΛS z) _ _ _) (conj H0 H1)).
Qed.

Theorem VL4 {T : lattice} (z : T) : forall a b : T, a ⊔ (a ⊓ b) = a.
Proof.
move=> a b.
(* Por dualidad *)
reflect_goal z [:: a ; b] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@ΛL4 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1)) ).
Qed.

(* Rp *)

Lemma RpJ {T : lattice} (z : T) : forall a b c : T, a ≤ b -> c ⊔ a ≤ (c ⊔ b).
Proof.
move=> a b c H.
apply (VS z).
split.
  by move: (VK z c b).
by move: ((τ _ _ _) H (VK' z c b) ).
Qed.

Lemma RpM {T : lattice} (z : T) : forall a b c : T, a ≤ b -> c ⊓ a ≤ (c ⊓ b).
Proof.
move=> a b c.
(* Por dualidad *)
reflect_goal z [:: a ; b ; c] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@RpJ L0 z0) (eval L0 z0 env0 (Var 1)) (eval L0 z0 env0 (Var 0))
                       (eval L0 z0 env0 (Var 2)) ).
Qed.

(* Teorema 6 *)

Theorem Thm6_1 {T : lattice} (z : T) : forall a b c : T, ((a ⊓ b) ⊔ (a ⊓ c)) ≤ (a ⊓ (b ⊔ c)).
Proof.
move=> a b c.
move: (VK z b c).
move=> /((RpM z) b (b ⊔ c) a) => H0.
move: (VK' z b c).
move=> /((RpM z) c (b ⊔ c) a) => H1.
by move: (((VS z) (a ⊓ b) (a ⊓ c) (a ⊓ (b ⊔ c))) (conj H0 H1) ).
Qed.

Theorem Thm6_2 {T : lattice} (z : T) : forall a b c : T, (a ⊔ (b ⊓ c)) ≤ ((a ⊔ b) ⊓ (a ⊔ c)).
Proof.
move=> a b c.
(* Por dualidad *)
reflect_goal z [:: a ; b ; c] meetT joinT.
apply reflectDual.
rewrite Dual/dual/dual_t/Teorema => L0 z0 env0.
rewrite /eval_f.
by move: ((@Thm6_1 L0 z0) (eval L0 z0 env0 (Var 0)) (eval L0 z0 env0 (Var 1))
                       (eval L0 z0 env0 (Var 2)) ).
Qed.

(* 3._ Lattices distributivas *)

Definition Distributive {T : lattice} := forall a b c : T, 
    ( (a ⊓ (b ⊔ c)) = ((a ⊓ b) ⊔ (a ⊓ c)) ).


Theorem Thm7 {T : lattice} (z : T) : (forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ c)) 
                                 <-> (@Distributive T).
Proof.
split; last first.
  rewrite /Distributive => H.
  move=> a b c.
  move: (H a b c) => /(semil z)-H1. 
  move: (ΛK' z a c) => /(RpJ z _ _ (a ⊓ b)).
  move: H1.
  apply: (τ _ _ _).
move=> H a b c.
move: (ΛK z a (b ⊔ c)) => H0.
move: (conj H0 (H a b c)).
rewrite MH [(a ⊓ b) ⊔ c](VL2 z) => H1.
move: (H a c (a ⊓ b))=> H2.
move: (τ _ _ _ H1 H2).
rewrite [(a ⊓ c) ⊔ (a ⊓ b)](VL2 z) => H3.
move: ((Thm6_1 z) a b c) => H4.
by move: (σ _ _ H4 H3).
Qed.

Lemma jW {T : lattice} (z : T) : forall a : T, a ⊔ a ≤ a.
Proof.
move=> a.
move: (reflex a)=> H.
rewrite -JH.
by split.
Qed.

(* Teorema 8 *)

Theorem Thm9 {T : lattice} (z : T) : (forall a b c : T, (a ⊓ b ≤ c /\ a ≤ (b ⊔ c)) -> (a ≤ c))
                                 <-> (@Distributive T).
Proof.
split; last first.
  rewrite -(Thm7 z) => H.
  move=> a b c [H0 H1].
  move: ((ΛW z) a)=> H2.
  move: (RpM z _ _ a H1) => H3.
  move: (τ _ _ _ H2 H3)=> H4.
  move: (τ _ _ _ H4 (H a b c)) => H5.
  move: (RpJ z _ _ c H0).
  rewrite (VL2 z) => H6.    
  move: (τ _ _ _ H6 ((jW z) c)) => H7.
  by move: (τ _ _ _ H5 H7).
move => H.
have Aux : forall a b c : T, (a ⊓ (b ⊔ c)) ≤ ((a ⊓ b) ⊔ c).
  move=> a b c.
  move: (VK z (a ⊓ b) c).
  rewrite -{1}(ΛL4 z b c) [b ⊓ _](ΛL2 z) (ΛL3 z)=> H0.
  move: (ΛK' z a (b ⊔ c)).
  rewrite -{2}(VL4 z b a) [_ ⊓ a](ΛL2 z) -(VL3 z)=> H1.
  by move: ((H (a ⊓ (b ⊔ c)) b ((a ⊓ b) ⊔ c)) (conj H0 H1) ).
by rewrite -(Thm7 z).
Qed.

Lemma Corol9_1 {T : lattice} (z : T) : (forall a b c : T, (a ⊓ c ≤ (b ⊓ c) /\ a ⊔ c ≤ (b ⊔ c)) -> (a ≤ b))
                                 <-> (@Distributive T).
Proof.
rewrite -(Thm9 z).
split.
  move => H.
  move => a c b.
  move: (H a b c).
  rewrite -MH -JH [c ⊔ b](VL2 z) => H0 [H1 H3].
  move: (ΛK' z a c) => H2.
  move: (VK' z b c) => H4.
  apply: H0.
  split.
    by split.
  by split.
move => H a c b.
rewrite -MH -JH.
move=> [[H0 H1] [H2 H3]].
apply: (H a b c).
rewrite [b ⊔ c](VL2 z).
by split.
Qed.

Lemma Corol9_2 {T : lattice} (z : T) : (@Distributive T)
                -> (forall a b c : T, (a ⊓ c = (b ⊓ c) /\ a ⊔ c = (b ⊔ c)) -> (a = b)).
Proof.
rewrite -(Corol9_1 z) => H.
move=> a b c /dobl.
move=> [[/(semil z _ _)-H0 /(semil z _ _)H1] [/(semir z _ _)-H2 /(semir z _ _)H3]].
apply: σ.
apply: (H a b c).
by split.
apply: (H b a c).
by split.
Qed.

(* Sección C Lattices de Skolem *)


Structure implicativeLattice := ImplicativeLattice 
  {
    ImpL :> lattice;
    ply : ImpL -> ImpL -> ImpL;
    Imp_P1 : forall a b : ImpL, a ⊓ (ply a b) ≤ b;
    Imp_P2 : forall a b c : ImpL, a ⊓ c ≤ b -> c ≤ (ply a b)
  }.
Notation "x ⊃ y" := (@ply _ x y) (at level 50). (* \supset *)
Notation P1 := (Imp_P1 _).
Notation P2 := (Imp_P2 _).

Theorem LMono {T : implicativeLattice} (z : T) : forall a b c: T, a ≤ b -> (b ⊃ c) ≤ (a ⊃ c).
Proof.
move=> a b c H.
move: (RpM z _ _ (b ⊃ c) H).
rewrite (ΛL2 z) [_⊓ b](ΛL2 z) => H0.
move: (P1 b c) => H1.
move: (τ _ _ _ H0 H1).
by move=> /P2.
Qed.

Theorem RMono {T : implicativeLattice} (z : T) : forall a b c: T, a ≤ b -> (c ⊃ a) ≤ (c ⊃ b).
Proof.
move=> a b c H1.
move: (P1 c a)=> H0.
move: (τ _ _ _ H0 H1).
by move=> /P2.
Qed.

Theorem Unidad {T : implicativeLattice} (z : T) : forall a : T, exists u, a ≤ u.
Proof.
move=> a.
move: (ΛK z a a).
move=> /P2-H.
by exists (a⊃a).
Qed.

Theorem Thm4_1_i {T : implicativeLattice} (z : T) : forall a b : T, b ≤ (a ⊃ b).
Proof.
move=> a b.
by move: (ΛK' z a b)=> /P2.
Qed.

Theorem Thm4_1_ii1 {T : implicativeLattice} (z : T) 
        : forall a b c : T, (a ⊃ (b ⊃ c) = (a ⊓ b)⊃ c).
Proof.
move=> a b c.
apply: σ.
  move: (P1 a (b ⊃ c)).
  move=> /(RpM z _ _ b).
  rewrite (ΛL3 z) [b ⊓ a](ΛL2 z)=> H0.
  move: (P1 b c)=> H1.
  move: (τ _ _ _ H0 H1).
  by move=> /P2.
move: (P1 (a ⊓ b) c).
rewrite -(ΛL3 z) [b ⊓ _](ΛL2 z) (ΛL3 z) (ΛL2 z).
by move=> /(P2 b c (a ⊓ ((a ⊓ b) ⊃ c))) /P2.
Qed.

Theorem Thm4_1_ii2 {T : implicativeLattice}  (z : T)
        : forall a b c : T, ((a ⊓ b) ⊃ c = b ⊃ (a ⊃ c)).
Proof.
move=> a b c.
move: (Thm4_1_ii1 z b a c).
by rewrite (ΛL2 z).
Qed.

Lemma RpM2 {T : lattice} (z : T) : forall a b c d : T,
  (a ≤ b) -> (c ≤ d) -> (a ⊓ c ≤ (b ⊓ d)).
Proof.
move=> a b c d H0 H1.
move: ((τ _ _ _) (ΛK z a c) H0)=> H2.
move: ((τ _ _ _) (ΛK' z a c) H1)=> H3.
by move: ((ΛS z _ _ _) (conj H2 H3)).
Qed.

Theorem Thm4_1_iii {T : implicativeLattice}  (z : T) : forall a b c : T,
     (a ⊃ (b ⊃ c) ≤ ((a ⊃ b) ⊃ (a ⊃ c))).
Proof.
move=> a b c.
move: (ΛW z a)=> /((RpM z) _ _ ((a⊃b)⊓(a⊃(b⊃c)))).
rewrite (ΛL3 z) {2}[_ ⊓ a](ΛL2 z) (ΛL3 z).
rewrite -[((a ⊓ (a ⊃ b))⊓_)⊓a](ΛL3 z) [(a ⊃ (b ⊃ c)) ⊓ a](ΛL2 z)=> H0.
move: (P1 a b) (P1 a (b ⊃ c))=> H1 H2.
move: (((RpM2 z) _ _ _ _) H1 H2)=> H3.
move: ((τ _ _ _) H0 H3)=> H4.
move: ((τ _ _ _) H4 (P1 b c)).
rewrite (ΛL2 z).
by move=> /P2/P2.
Qed.

Theorem Thm4_1_iv {T : implicativeLattice}  (z : T) : forall a b c : T,
     (a ⊃ (b ⊓ c) = ((a ⊃ b) ⊓ (a ⊃ c))).
Proof.
move=> a b c.
apply: σ.
  move:(ΛK z b c) (ΛK' z b c).
  move=> /((RMono z) (b ⊓ c) b a )-H0 /((RMono z) (b ⊓ c) c a )-H1.
  by move: (((ΛS z) _ _ _) (conj H0 H1)).
move: (((RpM2 z)_ _ _ _) (ΛW z a) (ρ ((a⊃b)⊓(a⊃c))) ).
rewrite -(ΛL3 z) [_⊓ ((a ⊃ b) ⊓ (a ⊃ c))](ΛL3 z).
rewrite (ΛL3 z) [_⊓(a ⊓ (a ⊃ b))](ΛL2 z).
rewrite -[((a ⊓ (a ⊃ b))⊓_)⊓_](ΛL3 z)=> H0.
move: ((RpM2 z _ _ _ _) (P1 a b) (P1 a c))=> H1.
move: ((τ _ _ _) H0 H1).
by rewrite -(ΛL3 z)=> /P2.
Qed.


