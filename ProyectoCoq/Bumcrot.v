From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.
From ProyectoCoq Require Import Dualidad.
From ProyectoCoq Require Import Dualidad_Bumcrot.
From ProyectoCoq Require Import MathCompLattices_SeqEnv.

Theorem Bumcrot1 {L : bumcrotLattice} (z : L) : forall a b caub canb : L, 
                 (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) 
                 -> (exists ca, (Comp a ca)) /\ (exists cb, (Comp b cb)).
Proof.
move=> a b caub canb [H0 H1] [H2 H3].
split.
  exists (caub ⊔ (canb ⊓ b)).
  split.
    move: ((Mod L))=> Modu.
    rewrite -(L4 z a b).
    rewrite (L1 z) -[_⊔ (caub ⊔ _)](L1 z) [_⊔ caub](L2 z).
    rewrite [(caub ⊔ _) ⊔ _](L1 z) -(L1 z).
    move: (mab_leq_ab z a b)=> /proj2.
    move=> /(Modu _ canb)-HMod1.
    rewrite HMod1.
    rewrite H2 [_ ⊓ b](L2d z) (amTop z).
    by rewrite (L2 z) -(L1 z) [b ⊔ a](L2 z) H0.
  move: (@Modular2 L z (Mod L))=> Mod2.
  rewrite -(L4d z a b).
  have aux : canb ⊓ b ≤ (a ⊔ b).
    move: (ab_leq_jab z a b)=>/proj2-Haub.
    move: (mab_leq_ab z canb b)=>/proj2-Hb.
    by move: (trans _ _ _ Hb Haub).
  move: aux => /(Mod2 _ caub)-HMod2. 
  rewrite (L1d z) HMod2 H1.
  rewrite (L2 z) (ajBot z).
  by rewrite [_ ⊓ b](L2d z) -(L1d z) H3.
exists (caub ⊔ (canb ⊓ a)).
split.
  move: (Mod L)=> Mod.
  rewrite -(L4 z b a).
  rewrite (L1 z) -[_⊔ (caub ⊔ _)](L1 z) [_⊔ caub](L2 z).
  rewrite [(caub ⊔ _) ⊔ _](L1 z) -(L1 z).
  move: (mab_leq_ab z b a)=> /proj2.
  move=> /(Mod _ canb)-HMod1.
  rewrite HMod1.
  rewrite [b ⊓ _](L2d z) H2 [_ ⊓ a](L2d z) (amTop z).
  by rewrite (L2 z) -(L1 z) H0.
move: (@Modular2 L z (Mod L))=> Mod2.
rewrite -(L4d z b a) [b ⊔ a](L2 z).
have aux : canb ⊓ a ≤ (a ⊔ b).
  move: (ab_leq_jab z a b)=>/proj1-Haub.
  move: (mab_leq_ab z canb a)=>/proj2-Ha.
  by move: (trans _ _ _ Ha Haub).
move: aux => /(Mod2 _ caub)-HMod2. 
rewrite (L1d z) HMod2 H1.
rewrite (L2 z) (ajBot z).
by rewrite (L2d z) (L1d z) (L2d z) H3.
Qed.

Theorem AuxBumcrot {L : bumcrotLattice} (z : L) : forall a b caub canb : L, 
                 (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) 
                 -> ((Comp a (caub ⊔ (canb ⊓ b)) ) /\ (Comp b (caub ⊔ (canb ⊓ a)))).
Proof.
move=> a b caub canb [H0 H1] [H2 H3]. 
move: (Mod L) (@Modular2 L z (Mod L))=> Modu Modu2.
split.
  split.
    rewrite -(L4 z a b).
    rewrite (L1 z) -[_⊔ (caub ⊔ _)](L1 z) [_⊔ caub](L2 z).
    rewrite [(caub ⊔ _) ⊔ _](L1 z) -(L1 z).
    move: (mab_leq_ab z a b)=> /proj2.
    move=> /(Modu _ canb)-HMod1.
    rewrite HMod1.
    rewrite H2 [_ ⊓ b](L2d z) (amTop z).
    by rewrite (L2 z) -(L1 z) [b ⊔ a](L2 z) H0.
  rewrite -(L4d z a b).
  have aux : canb ⊓ b ≤ (a ⊔ b).
    move: (ab_leq_jab z a b)=>/proj2-Haub.
    move: (mab_leq_ab z canb b)=>/proj2-Hb.
    by move: (trans _ _ _ Hb Haub).
  move: aux => /(Modu2 _ caub)-HMod2. 
  rewrite (L1d z) HMod2 H1.
  rewrite (L2 z) (ajBot z).
  by rewrite [_ ⊓ b](L2d z) -(L1d z) H3.
split.
  rewrite -(L4 z b a).
  rewrite (L1 z) -[_⊔ (caub ⊔ _)](L1 z) [_⊔ caub](L2 z).
  rewrite [(caub ⊔ _) ⊔ _](L1 z) -(L1 z).
  move: (mab_leq_ab z b a)=> /proj2.
  move=> /(Modu _ canb)-HMod1.
  rewrite HMod1.
  rewrite [b ⊓ _](L2d z) H2 [_ ⊓ a](L2d z) (amTop z).
  by rewrite (L2 z) -(L1 z) H0.
rewrite -(L4d z b a) [b ⊔ a](L2 z).
have aux : canb ⊓ a ≤ (a ⊔ b).
  move: (ab_leq_jab z a b)=>/proj1-Haub.
  move: (mab_leq_ab z canb a)=>/proj2-Ha.
  by move: (trans _ _ _ Ha Haub).
move: aux => /(Modu2 _ caub)-HMod2. 
rewrite (L1d z) HMod2 H1.
rewrite (L2 z) (ajBot z).
by rewrite (L2d z) (L1d z) (L2d z) H3.
Qed.

Theorem AuxBumcrotd {L : bumcrotLattice} (z : L) : forall a b caub canb : L, 
                 (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) 
                 -> ((Comp a (canb ⊓ (caub ⊔ b)) ) /\ (Comp b (canb ⊓ (caub ⊔ a)))).
Proof.
move=> a b caub canb.
(* Prueba por dualidad *)
rewrite /Comp.
reflectB_goal z [:: a; b; caub; canb] meetT joinT.
apply reflectDualB.
rewrite DualB /dualB /dualB_t => L0 z0 env0.
rewrite /evalB_f /evalB.
move: ((@AuxBumcrot L0 z0) (evalB L0 z0 env0 (VarB 0)) (evalB L0 z0 env0 (VarB 1))
                                    (evalB L0 z0 env0 (VarB 3)) (evalB L0 z0 env0 (VarB 2))  ).
rewrite /Comp /evalB.
move=> H [H0 H1] [H2 H3].
move: ((H (conj H3 H2)) (conj H1 H0)).
move=> [[B0 B1] [B2 B3]].
by [].
Qed.

Definition C_unico {L : bumcrotLattice} (a : L) := forall b c : L, (Comp a b) /\ (Comp a c) -> b = c.

Lemma auxCompBumcrot {L : bumcrotLattice} (z : L) : forall a b ca cb canb caub : L,
                     (C_unico a) -> (C_unico b) -> (Comp a ca) -> (Comp b cb)
                  -> (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) ->
                   (ca = caub ⊔ (canb ⊓ b)) /\ (cb = caub ⊔ (canb ⊓ a)).
Proof.
move=> a b ca cb canb caub CompUa CompUb Comp_a Comp_b H0 H1.
split.
  apply: CompUa.
  split.
    by [].
  move: (AuxBumcrot z a b caub canb).
  by move=> /(_ H0)/(_ H1)/proj1.
apply: CompUb.
split.
  by [].
move: (AuxBumcrot z a b caub canb).
by move=> /(_ H0)/(_ H1)/proj2.
Qed.

Lemma auxCompBumcrotD {L : bumcrotLattice} (z : L) : forall a b ca cb canb caub : L,
                     (C_unico a) -> (C_unico b) -> (Comp a ca) -> (Comp b cb)
                      -> (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) ->
                     (ca = canb ⊓ (caub ⊔ b) /\ cb = canb ⊓ (caub ⊔ a)).
Proof.
move=> a b ca cb canb caub CompUa CompUb Comp_a Comp_b H0 H1.
split.
  apply: CompUa.
  split.
    by [].
  move: (AuxBumcrotd z a b caub canb).
  by move=> /(_ H0)/(_ H1)/proj1.
apply: CompUb.
split.
  by [].
move: (AuxBumcrotd z a b caub canb).
by move=> /(_ H0)/(_ H1)/proj2.
Qed.

Theorem Bumcrot2 {L : bumcrotLattice} (z : L) : forall a b ca cb canb caub : L,
                     (C_unico a) -> (C_unico b) -> (Comp a ca) -> (Comp b cb)
                      -> (Comp (a ⊔ b) caub) -> (Comp (a ⊓ b) canb) ->
                    (Comp (a ⊓ b) (ca ⊔ cb)) /\ (Comp (a ⊔ b) (ca ⊓ cb)).
Proof.
move=> a b ca cb canb caub CompUa CompUb Comp_a Comp_b H0 H1.
move: ((auxCompBumcrot z) a b ca cb canb caub CompUa CompUb Comp_a Comp_b H0 H1 ) => [HCa HCb].
move: ((auxCompBumcrotD z) a b ca cb canb caub CompUa CompUb Comp_a Comp_b H0 H1 ) => [HCad HCbd].
move: H0 => [H2 H3].
move: H1 => [H4 H5].
split.
  split.
    rewrite HCa HCb [_ ⊔ (caub ⊔ _)](L1 z) -[(canb ⊓ b) ⊔ (caub ⊔ (canb ⊓ a))](L1 z).
    rewrite [_ ⊔ caub](L2 z) (L1 z) -[caub ⊔ (caub ⊔ _)](L1 z).
    rewrite (L3 z) -[_ ⊔ (caub ⊔ _)](L1 z) [_ ⊔ caub](L2 z).
    rewrite (L1 z) -[_ ⊔ ((canb ⊓ b) ⊔ _)](L1 z) -(L3 z (a ⊓ b)).
    rewrite (L1 z) [((a ⊓ b) ⊔ (a ⊓ b)) ⊔ _](L1 z).
    rewrite -[(a ⊓ b) ⊔ ((canb ⊓ b) ⊔ (canb ⊓ a))](L1 z).
    rewrite [_ ⊔ (canb ⊓ b)](L2 z) [(_ ⊔ (a ⊓ b)) ⊔ _](L1 z).
    rewrite -[(a ⊓ b) ⊔ (_ ⊔ _)](L1 z).
    move: (Mod L). rewrite /Modu_L => Mod.
    move: (mab_leq_ab z a b)=> [A B].
    move: A => /(Mod _ canb)-HModa.
    move: B => /(Mod _ canb)-HModb.
    rewrite HModa HModb H4.
    rewrite (L2d z) [_ ⊓ a](L2d z) (amTop z) (amTop z).
    by rewrite (L2 z) [b ⊔ a](L2 z) H2.
  move: ((ModularD z) (Mod L))=> /(ModularD2 z)-ModD.
  rewrite HCad HCbd.
  move: (mab_leq_ab z canb (caub ⊔ a))=> /proj1.
  move=> /(ModD _ (caub ⊔ b))=> HModD.
  rewrite -HModD -(L1d z) H5.
  move: (TB ((caub ⊔ b) ⊔ (canb ⊓ (caub ⊔ a))))=> /proj2.
  by rewrite (ConnectM z) (L2d z).
split.
  move: (Mod L)=> /(ModularD z)-ModD.
  rewrite HCa HCb.
  move: (ab_leq_jab z caub (canb ⊓ a))=> /proj1.
  move=> /(ModD _ (canb ⊓ b))-HModD.
  rewrite -HModD -(L1 z) H2 (L2 z).
  move: ( TB ((canb ⊓ b) ⊓ (caub ⊔ (canb ⊓ a))))=> /proj1.
  by rewrite ConnectJ.
move: (Mod L)=> /(Modular2 z)-Mod.
rewrite HCad (L1d z) [_ ⊓ cb](L2d z) -[_ ⊓ (cb ⊓_)](L1d z).
rewrite HCbd -(L1d z) -[canb ⊓ (canb ⊓ _)](L1d z).
rewrite (L3d z) -[(a ⊔ b) ⊓ (canb ⊓ _)](L1d z) [_ ⊓ canb](L2d z).
rewrite (L1d z) (L1d z) -[(a ⊔ b) ⊓ (_ ⊓ _)](L1d z) -(L3d z (a ⊔ b)).
rewrite [(_ ⊓ _) ⊓ (caub ⊔ a)](L1d z) [(a ⊔ b) ⊓ _](L2d z).
rewrite [(_ ⊓ (a ⊔ b)) ⊓ (caub ⊔ b)](L1d z).
move: (ab_leq_jab z a b)=> [A B].
move: A => /(Mod _ caub)-HModa.
move: B => /(Mod _ caub)-HModb.
rewrite HModa HModb H3.
rewrite (L2 z) [_ ⊔ b](L2 z) (ajBot z) (ajBot z).
by rewrite (L2d z) H5.
Qed.