From mathcomp Require Import all_ssreflect.
From ProyectoCoq Require Import Def_Lattice.
From ProyectoCoq Require Import Dualidad.
From ProyectoCoq Require Import MathCompLattices_SeqEnv.

Structure bumcrotLattice := BumcrotLattice 
  {
    BumL :> boundedLattice;
    Mod: (@Modu_L BumL)
  }.

Inductive TermB : Set :=
| TopB : TermB
| BotB : TermB
| VarB  : nat -> TermB
| MeetB : TermB -> TermB -> TermB
| JoinB : TermB -> TermB -> TermB.

Fixpoint evalB (L : bumcrotLattice) (z : L) (env : seq L) (t : TermB) : L :=
  match t with
  | TopB        => top
  | BotB        => bot
  | VarB n      => nth z env n
  | MeetB t1 t2 => @meetT L (evalB L z env t1) (evalB L z env t2)
  | JoinB t1 t2 => @joinT L (evalB L z env t1) (evalB L z env t2)
  end.

Inductive FormB : Set :=
| fb_leq  : TermB -> TermB -> FormB
| fb_eq   : TermB -> TermB -> FormB
| fb_neg  : FormB -> FormB
| fb_conj : FormB -> FormB -> FormB
| fb_or   : FormB -> FormB -> FormB
| fb_imp  : FormB -> FormB -> FormB.

Fixpoint evalB_f (L : bumcrotLattice) (z : L) (env : seq L) (f : FormB) : Prop :=
  match f with
  | fb_leq t1 t2 => (evalB L z env t1) ≤ (evalB L z env t2)
  | fb_eq t1 t2  => (evalB L z env t1) = (evalB L z env t2)
  | fb_neg f1     => ~ (evalB_f L z env f1)
  | fb_conj f1 f2  => evalB_f L z env f1 /\ evalB_f L z env f2
  | fb_or f1 f2    => (evalB_f L z env f1) \/ (evalB_f L z env f2)
  | fb_imp f1 f2   =>  (evalB_f L z env f1) -> (evalB_f L z env f2)
  end.

Fixpoint dualB_t (t : TermB) : TermB :=
  match t with
  | TopB  => BotB
  | BotB  => TopB
  | VarB n => VarB n
  | MeetB t1 t2 => JoinB (dualB_t t1) (dualB_t t2)
  | JoinB t1 t2 => MeetB (dualB_t t1) (dualB_t t2)
  end.

Fixpoint dualB (f : FormB) : FormB :=
  match f with
  | fb_leq t1 t2 => fb_leq (dualB_t t2) (dualB_t t1)
  | fb_eq t1 t2  => fb_eq (dualB_t t1) (dualB_t t2)
  | fb_neg f1     => fb_neg (dualB f1)
  | fb_conj f1 f2  => fb_conj (dualB f1) (dualB f2)
  | fb_or f1 f2    => fb_or (dualB f1) (dualB f2)
  | fb_imp f1 f2   => fb_imp (dualB f1) (dualB f2)
  end.

Canonical Structure dual_bounded_lattice_of (L : boundedLattice) : boundedLattice :=
  BoundedLattice
    (dual_lattice_of L) (Bot L) (Top L)  (fun a => 
      let '(conj Htop Hbot) := Top_Bottom L a in
      conj Hbot Htop) .


Lemma le_dualBound (L : boundedLattice) (x y : L) :
  (ord (dual_bounded_lattice_of L) x y) <-> (ord L y x).
Proof.
by [].
Qed.

Lemma le_dualj (L : boundedLattice) (x y : L) :
  (@joinT (dual_bounded_lattice_of L) x y) = (@meetT L x y).
Proof.
by [].
Qed.

Lemma le_dualm (L : boundedLattice) (x y : L) :
  (@meetT (dual_bounded_lattice_of L) x y) = (@joinT L x y).
Proof.
by [].
Qed.


Lemma modular_dual (L : boundedLattice) (z : L) (P : @Modu_L L) : @Modu_L (dual_bounded_lattice_of L).
Proof.
  rewrite /Modu_L.
  move=> p q r.
  rewrite le_dualBound le_dualj le_dualj le_dualm le_dualm.
  by move: ((@Modular2 L z P) r q p).
Qed.

Canonical Structure dual_bumcrot_lattice_of (B : bumcrotLattice) (z : B) : bumcrotLattice :=
  BumcrotLattice
    (dual_bounded_lattice_of B)
    (modular_dual (B) z (Mod B)).


Lemma jldmB : forall (L : bumcrotLattice) (z : L) , joinT (dual_bumcrot_lattice_of L z) = meetT L.
Proof.
  by [].
Qed.

Lemma mldjB : forall (L : bumcrotLattice) (z : L), meetT (dual_bumcrot_lattice_of L z) = joinT L.
Proof.
  by [].
Qed.

Lemma  evalB_m : forall (L : bumcrotLattice) (z : L) (env : seq L) (t0 t1 : TermB), 
              evalB L z env (MeetB t0 t1) = meetT L (evalB L z env t0) (evalB L z env t1).
Proof. by move=> L0 env0; rewrite /evalB. Qed.

Lemma evalB_j : forall (L : bumcrotLattice) (z : L) (env : seq L) (t0 t1 : TermB), 
              evalB L z env (JoinB t0 t1) = joinT L (evalB L z env t0) (evalB L z env t1).
Proof. by move=> L0 env0; rewrite /evalB. Qed.

Lemma evalB_conj : forall (L : bumcrotLattice) (z : L) (env : seq L) (f0 f1 : FormB), 
                   evalB_f L z env (fb_conj f0 f1) = and (evalB_f L z env f0) (evalB_f L z env f1).
Proof.  by []. Qed.

Lemma dualB_conj : forall (f0 f1 : FormB), dualB (fb_conj f0 f1) = fb_conj (dualB f0) (dualB f1).
Proof.  by []. Qed.

Lemma evalB_or : forall (L : bumcrotLattice) (z : L) (env : seq L) (f0 f1 : FormB), 
                   evalB_f L z env (fb_or f0 f1) = or (evalB_f L z env f0) (evalB_f L z env f1).
Proof.  by []. Qed.

Lemma dualB_or : forall (f0 f1 : FormB), dualB (fb_or f0 f1) = fb_or (dualB f0) (dualB f1).
Proof.  by []. Qed.

Lemma evalB_imp : forall (L : bumcrotLattice) (z : L) (env : seq L) (f0 f1 : FormB), 
                   evalB_f L z env (fb_imp f0 f1) =(( evalB_f L z env f0) -> (evalB_f L z env f1)).
Proof. by []. Qed.

Lemma dualB_imp : forall (f0 f1 : FormB), dualB (fb_imp f0 f1) = fb_imp (dualB f0) (dualB f1).
Proof.  by []. Qed.

Lemma dualB_m : forall t0 t1 : TermB, 
                dualB_t (MeetB t0 t1) = JoinB (dualB_t t0) (dualB_t t1).
Proof.  by move=> t2 t3; rewrite /dualB_t. Qed.

Lemma dualB_j : forall t0 t1 : TermB, 
                dualB_t (JoinB t0 t1) = MeetB (dualB_t t0) (dualB_t t1).
Proof.  by move=> t2 t3; rewrite /dualB_t. Qed.

Theorem eval_dualB (L : bumcrotLattice) (z : L) (env : seq L) (t : TermB) :
  evalB (dual_bumcrot_lattice_of L z) z env t = evalB L z env (dualB_t t).
Proof.
elim t.
  (* TopB *)
  by rewrite /evalB.
  (* BotB *)
  by rewrite /evalB.

  (* VarB n *)
  move=> n0.
  by rewrite {1}/evalB/dualB_t/evalB.
  
  (* MeetB t0 t1*)
  move=> t0 H0 t1 H1.
  rewrite dualB_m (evalB_j L z env).
  rewrite (evalB_m (dual_bumcrot_lattice_of L z) z env).
  by rewrite H0 H1 mldjB.

  (* JoinB t0 t1 *)
  move=> t0 H0 t1 H1.
  rewrite dualB_j (evalB_m L z env).
  rewrite (evalB_j (dual_bumcrot_lattice_of L z) z env).
  by rewrite H0 H1 jldmB.
Qed.

Lemma le_dualB (L : bumcrotLattice) (z : L) (x y : L) :
  (ord (dual_bumcrot_lattice_of L z) x y) <-> (ord L y x).
Proof.
by [].
Qed.

Theorem evalB_dual_f (L : bumcrotLattice) (z : L) (env : seq L) (f : FormB) :
  evalB_f (dual_bumcrot_lattice_of L z) z env f = evalB_f L z env (dualB f).
Proof.
elim f.
  (* Term *)
  move=> t0 t1.
  by rewrite /dualB /evalB_f eval_dualB eval_dualB.
  
  move=> t0 t1.
  by rewrite /dualB /evalB_f eval_dualB eval_dualB.
  
  (* Neg *)
  move=> f0 H0.
  have aux: forall (L : bumcrotLattice) (z : L) (env : seq L) (f0 : FormB), evalB_f L z env (fb_neg f0) = ~ (evalB_f L z env f0).
    by [].
  have auxd: forall (f0 : FormB), dualB (fb_neg f0) = fb_neg (dualB f0).
    by [].
  rewrite auxd aux aux.
  by rewrite H0.

  (* Conj *)
  move=> f0 H0 f1 H1.
  rewrite dualB_conj evalB_conj evalB_conj.
  by rewrite H0 H1.
  
  (* Or *)
  move=> f0 H0 f1 H1.
  rewrite dualB_or evalB_or evalB_or.
  by rewrite H0 H1.
  
  (* Imp *)
  move=> f0 H0 f1 H1.
  rewrite dualB_imp evalB_imp evalB_imp.
  by rewrite H0 H1.
Qed.


Lemma dualB_td : forall t : TermB, t = dualB_t (dualB_t t).
Proof.
move=> t; elim t.
  
  by rewrite /dualB_t.
  
  by rewrite /dualB_t.

  by rewrite /dualB_t.
  
  move=> t0 H0 t1 H1.
  by rewrite dualB_m dualB_j -H0 -H1.
  
  move=> t0 H0 t1 H1.
  by rewrite dualB_j dualB_m -H0 -H1.
Qed.

Lemma dualBd : forall F : FormB, F = dualB (dualB F).
Proof.
move=>F; elim F.
  by move=> t0 t1; rewrite /dualB {1}(dualB_td t0) {1}(dualB_td t1).

  by move=> t0 t1; rewrite /dualB {1}(dualB_td t0) {1}(dualB_td t1).

  by move=> F0 H0; rewrite {1}H0 {3 4}/dualB.

  by move=> F0 H0 F1 H1; rewrite dualB_conj dualB_conj -H0 -H1.

  by move=> F0 H0 F1 H1; rewrite dualB_or dualB_or -H0 -H1.

  by move=> F0 H0 F1 H1; rewrite dualB_imp dualB_imp -H0 -H1.
Qed.



Definition TeoremaB (F : FormB) : Prop :=
forall (L : bumcrotLattice) (z : L) (env : seq L), (evalB_f L z env F).

Theorem DualidadB : forall f : FormB, (TeoremaB f) -> (TeoremaB (dualB f)).
Proof.
move=> f.
elim f.
  move=> t0 t1.

    (* Caso: leq *)

    rewrite /dualB /TeoremaB => Hip L z env.
    move: (Hip (dual_bumcrot_lattice_of L z) z env).
    by rewrite evalB_dual_f /dualB.

    (* Caso: eq *)
    
    rewrite /TeoremaB /dualB /evalB_f => t0 t1 Hip L z env.
    move: (Hip (dual_bumcrot_lattice_of L z) z env).
    by rewrite eval_dualB eval_dualB.

    (* Caso: neg *)
    rewrite /TeoremaB => f0 _ Hip L z env.
    move: (Hip (dual_bumcrot_lattice_of L z) z env).
    have aux: forall (L : bumcrotLattice) (z : L) (env : seq L) (f0 : FormB), evalB_f L z env (fb_neg f0) = ~ (evalB_f L z env f0).
      by [].
    have auxd: forall (f0 : FormB), dualB (fb_neg f0) = fb_neg (dualB f0).
      by [].
    rewrite auxd aux aux.
    by rewrite evalB_dual_f.

    (* Caso: Conj *)
    rewrite /TeoremaB => f0 _ f1 _ Hip L z env.
    move: (Hip (dual_bumcrot_lattice_of L z) z env).
    rewrite dualB_conj evalB_conj evalB_conj.
    by rewrite evalB_dual_f evalB_dual_f.

    (* Caso: Or *)
    rewrite /TeoremaB => f0 _ f1 _ Hip L z env.
    move: (Hip (dual_bumcrot_lattice_of L z) z env).
    rewrite dualB_or evalB_or evalB_or.
    by rewrite evalB_dual_f evalB_dual_f.

    (* Caso: Imp *)
    rewrite /TeoremaB => f0 _ f1 _ Hip L z env.
    move: (Hip (dual_bumcrot_lattice_of L z) z env).
    rewrite dualB_imp evalB_imp evalB_imp.
    by rewrite evalB_dual_f evalB_dual_f.
Qed.
(*    Fin del Teorema de dualidad para lattices acotadas     *)

Lemma DualB : forall f : FormB, (TeoremaB f) <-> (TeoremaB (dualB f)).
Proof.
move=> f.
split.
  by move: (DualidadB f).
move: (DualidadB (dualB f))=> H.
by rewrite {2}(dualBd f).
Qed.


(* Ltac para Bumcrot *)

Ltac rankB env n v :=
  match env with
  | (cons ?X1 ?X2) =>
      let env' := constr:(X2) in
        match constr:(X1 = v) with
        | (?X1 = ?X1) => n
        | _ => rankB env' (S n) v
        end
  end.

Ltac reflectB env m j v :=
  match v with
  | (m _ ?X1 ?X2) =>
      let r1 := reflectB env m j X1
      with r2 := reflectB env m j X2 in
        constr:(MeetB r1 r2)
  | (j _ ?X1 ?X2) =>
      let r1 := reflectB env m j X1
      with r2 := reflectB env m j X2 in
        constr:(JoinB r1 r2)
  | ?X1 =>
      let n := rankB env 0 X1 in
        constr:(VarB n)
  | top => constr:(TopB)
  | bot => constr:(BotB)
  | _ => constr:(VarB 0)
  end.

Ltac reflect_formB env m j f :=
  lazymatch f with
  | ?x ≤ ?y =>
        let rx := reflectB env m j x in
        let ry := reflectB env m j y in
        constr:(fb_leq rx ry)
  | ?x = ?y =>
        let rx := reflectB env m j x in
        let ry := reflectB env m j y in
        constr:(fb_eq rx ry)
  | ~ ?p =>
        let rp := reflect_formB env m j p in
        constr:(fb_neg rp)
  | ?p /\ ?q =>
        let rp := reflect_formB env m j p in
        let rq := reflect_formB env m j q in
        constr:(fb_conj rp rq)
  | ?p \/ ?q =>
        let rp := reflect_formB env m j p in
        let rq := reflect_formB env m j q in
        constr:(fb_or rp rq)
  | ?p -> ?q =>
        let rp := reflect_formB env m j p in
        let rq := reflect_formB env m j q in
        constr:(fb_imp rp rq)
  | _ => fail "reflect_form: No reconozco esta forma:" f
  end.

Lemma reflect_sound_fullB (L : bumcrotLattice) (z : L) (env : seq L) (f : FormB) :
  evalB_f L z env f <-> evalB_f L z env f.
Proof. by []. Qed.

Ltac reflectB_goal z env m j :=
  match goal with
  | |- ?G =>
      let FG := reflect_formB env m j G in
      apply (proj1 (reflect_sound_fullB _ z env FG))
  end.

Lemma reflectDualB (L : bumcrotLattice) (z : L) (env : seq L) (F : FormB) : TeoremaB (F) -> evalB_f L z env F.
Proof.
rewrite /TeoremaB=> H.
by move: (H L z env).
Qed.