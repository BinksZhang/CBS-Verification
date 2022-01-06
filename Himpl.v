(**

This file describes the representation and properties of CBS-heap predicates.

Author: Bowen Zhang.

Date : 2022.01.06
*)

Set Implicit Arguments.
From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* CBS *) Require Export Language InnerPre.

(*** ============  CBS-heap predicates ====================== ***)
Definition hprop := heap -> Prop.

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

Open Scope hprop_scope.

Definition qimpl {A} (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Types Hb : hbprop.
Implicit Types Hf : hfprop.
Implicit Types Qb : val->hbprop.
Implicit Types Qf : val->hfprop.


Definition getheapf (h:heap): heapf :=
  match h with (hf,hb) => hf end.
Definition getheapb (h:heap): heapb :=
  match h with (hf,hb) => hb end.

Notation "h '`f' " := (getheapf h)
  (at level 20) : heap_scope.
Notation "h '`b' " := (getheapb h)
  (at level 20) : heap_scope.

Open Scope heap_scope.

Lemma state_get_eq : forall h, h = (h `f, h `b).
Proof. 
  destruct h. simpl. reflexivity. Qed.

Definition glounion h1 h2 := 
  (h1`f \+ h2`f, h1`b \+ h2`b).

Definition glodisjoint h1 h2 := 
  Fmap.disjoint (h1`f) (h2`f) /\ Fmap.disjoint (h1`b) (h2`b).

Notation "h1 \g h2" := (glounion h1 h2)
  (at level 37, right associativity).

Notation "h1 _|_ h2" := ( glodisjoint h1 h2)
  (at level 37, right associativity).

(* ================================================================= *)
(** Core CBS heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal 
    - [ H1 \-* H2 ] denotes the magic wand
**)


Definition RefineAssn (Hf:hfprop) (Hb:hbprop): hprop := 
  fun h => Hf (h`f) /\ Hb (h`b).

Notation "'\R[' Hf ',' Hb ']'" := (RefineAssn Hf Hb) (at level 50) : hprop_scope.

(* empty *)

Definition hempty : hprop :=
  fun h => (h`f) = Fmap.empty /\ (h`b) = Fmap.empty.

Definition hexists {A:Type} (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Definition hforall {A : Type} (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Definition hstar (H1 H2:hprop): hprop := 
  fun h => exists h1 h2, 
    H1 h1 
  /\ H2 h2
  /\ h1 _|_ h2
  /\ h = h1 \g h2.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ ' x1 .. xn , '/ ' H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ ' x1 .. xn , '/ ' H ']'") : hprop_scope.

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

(** ------------ CBS Assn himpl --------  **)
Lemma himpl_inv : forall H1 H2 h,
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma himpl_refl : forall H,
  H ==> H.
Proof. introv M. auto. Qed.

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof. intros. unfolds*. intros. apply himpl_refl. Qed.

Hint Resolve himpl_refl qimpl_refl state_get_eq.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] (hf_empty,hb_empty).
Proof. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = (hf_empty,hb_empty).
Proof.
  introv M.
  destruct M as (M1&M2).
  rewrite <- M1,<- M2.
  auto.
 Qed.

Lemma hempty_refine : 
  \[] = \R[\f[],\b[]].
Proof. unfolds*. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hstar_sep_l : forall Hf Hb Hf' Hb',
  (\R[ Hf, Hb ]) \* (\R[ Hf', Hb'])
==>
  \R[(Hf \f* Hf'), (Hb \b* Hb')].
Proof.
  introv.
  introv M.
  destruct M as (h1&h2&HA&HB&(HC1&HC2)&HD).
  destruct HA as (HA1&HA2).
  destruct HB as (HB1&HB2).
  subst. splits; simpl.
  applys~ hfstar_intro.
  applys~ hbstar_intro.
Qed.

Lemma hstar_sep_r : forall Hf Hb Hf' Hb',
  \R[(Hf \f* Hf'), (Hb \b* Hb')]
==>
  (\R[ Hf, Hb ]) \* (\R[ Hf', Hb' ]).
Proof.
  introv.
  introv M.
  destruct M as (HA&HB).
  destruct HA as (sf1&sf2&HB1&HB2&HB3&HB4).
  destruct HB as (sb1&sb2&HC1&HC2&HC3&HC4).
  exists (sf1,sb1) (sf2,sb2). splits.
  splits~. splits~. splits~.
  unfold glounion. simpl.
  rewrite <- HB4, <- HC4.
  auto.
Qed.

Lemma hstar_sep: forall Hf Hb Hf' Hb',
  (\R[ Hf, Hb ]) \* (\R[ Hf', Hb' ])
=
  \R[(Hf \f* Hf'), (Hb \b* Hb')].
Proof.
  intros. apply himpl_antisym.
  apply hstar_sep_l.
  apply hstar_sep_r.
Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 -> H2 h2 ->
  Fmap.disjoint (h1`f) (h2`f) 
  /\ Fmap.disjoint (h1`b) (h2`b) 
  -> (H1 \* H2) (h1 \g h2).
Proof. intros. exists h1 h2. splits~. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ h1 _|_ h2 /\ h = h1 \g h2.
Proof.
  introv M1.
  destruct M1 as (h1&h2&MA&MB&MC&MD).
  exists~ h1 h2.
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof.
  applys hprop_op_comm. unfold hprop, hstar. intros H1 H2.
  intros h (h1&h2&HA&HB&(HC&HD)&HE).
  exists h2 h1.
  splits~. splits~.
  unfold glounion.
  rewrite~ Fmap.union_comm_of_disjoint.
  remember (h1 `f \+ h2 `f) as A.
  rewrite~ Fmap.union_comm_of_disjoint.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  - intros (h12&h3&M).
    destruct M as (M1&M2&(M3&M4)&M6).
    rewrite M6.
    destruct M1 as (h1&h2&MA&MB&(MC&MD)&MF).
    unfolds glounion.
    subst. simpls. exists h1 (h2 \g h3).
    splits~. applys~ hstar_intro.
    rewrite disjoint_union_eq_l in M3, M4.
    splits; simpl;
    rewrite~ disjoint_union_eq_r.
  - introv M.
    destruct M as (h1&h23&M1&M2&(M3&M4)&M6).
    destruct M2 as (h2&h3&MA&MB&(MC&MD)&MF).
    unfolds glounion. subst. simpls.
    exists (h1 \g h2) h3. splits~. applys~ hstar_intro.
    rewrite disjoint_union_eq_r in M3, M4.
    splits; simpl; rewrite~ disjoint_union_eq_l.
    unfold glounion. simpl.
    do 2 rewrite union_assoc. auto.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof.
  introv W. intros h M.
  destruct M as (h1&h2&MA&MB&MC).
  exists~ h1 h2.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof.
  introv M.
  do 2 rewrite (@hstar_comm H1).
  applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof.
  intros. applys himpl_antisym; intros h M.
  destruct M as (h1&h2&HA&HB&(HC&HD)&HF).
  unfold glounion in HF.
  apply hempty_inv in HA.
  subst. simpls. 
  do 2 rewrite union_empty_l.
  rewrite~ <- state_get_eq.
  
  exists (hf_empty,hb_empty) h.
  splits~. applys hempty_intro.
  splits; simpl; apply disjoint_empty_l. 
  unfold glounion. simpl.
  do 2 rewrite union_empty_l. auto.
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof.
  intros.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm.
  applys hstar_hempty_l.
Qed.

Lemma hstar_hempty_l' : forall H,
  \R[\f[],\b[]] \* H = H.
Proof.
  rewrite <- hempty_refine.
  intros. apply hstar_hempty_l.
Qed.

Lemma hstar_hempty_r' : forall H,
  (H \* \R[\f[],\b[]]) = H.
Proof.
  intros.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm.
  applys hstar_hempty_l.
Qed.


Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1.
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.


(* ----------------------------------------------------------------- *)
(** ***  Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] h_empty.
Proof. introv M. exists M. unfolds*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = h_empty.
Proof. introv (p&M). split~. apply~ hempty_inv. Qed.

Lemma hstar_hpure : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof. intros. rewrite* hstar_hpure. Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof. introv HP W. intros h K. rewrite* hstar_hpure. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof.
  introv M. rewrite <- hstar_hpure. rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof.
  introv M N. rewrite <- (hstar_hempty_l \[P]).
  rewrite hstar_comm. rewrite~ hstar_hpure.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof.
  introv W Hh. rewrite hstar_hpure in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof.
  applys himpl_antisym; intros h M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof.
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hexists] *)

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.
Proof. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof. intros. destruct H as [x H]. exists~ x. Qed.


(*========== some additional lemmas (useful in parctice) ==========*)

Lemma hbstar_comm3 : forall (H1 H2 H3 : hbprop),
   H1 \b* H2 \b* H3 = H3 \b* H2 \b* H1.
Proof.
  intros. rewrite <- hbstar_assoc, hbstar_comm.
  remember (H1 \b* H2) as E eqn:M.
  rewrite hbstar_comm in M. rewrite~ M.
Qed.

Lemma hstar_comm3 : forall (H1 H2 H3 : hprop),
   H1 \* H2 \* H3 = H2 \* H1 \* H3.
Proof.
  intros. rewrite <- hstar_assoc.
  remember (H1 \* H2) as E eqn:M.
  rewrite hstar_comm in M. rewrite M.
  rewrite~ hstar_assoc.
Qed.


Lemma listtoapp3 : forall (p1 p2 p3: bloc),
  (p1 :: p2 :: p3 :: nil) = (p1 :: p2 :: nil) ++ (p3 :: nil).
Proof. intros. rew_list~. Qed.

Lemma himpl_hbexists : forall Hf Hb l,
(fun x : val =>
 (\R[ \f[], \existsb bp0 : bloc, \b[x = val_bloc bp0] \b* bp0 ~b~> l]) \*
 (\R[ Hf, Hb])) ===>
(fun r : val =>
 \R[ Hf,
 \existsb bp' : bloc, \b[r = val_bloc bp'] \b* bp' ~b~> l \b* Hb]).
Proof.
  intros. intros r.
  rewrite hstar_sep.
  intros h (MA&MB). splits~.
  rewrite hfstar_hempty_l in MA. auto.
  rewrite hbstar_hexists in MB.
  destruct MB as (bp'&MB). rewrite hbstar_assoc in MB.
  exists~ bp'.
Qed.

Lemma himpl_hexists' : forall Hf bp l,
(fun x : val =>
 \exists bp0 : bloc,\[x = bp0] \* (\R[ \f[], bp0 ~b~> l]) \*
 (\R[ Hf, bp ~b~> l])) ===>
(fun r : val =>
 \exists bp' : bloc,\[r = bp'] \* (\R[ Hf, bp' ~b~> l \b* bp ~b~> l])).
Proof.
  intros. intros r h M.
  destruct M as (bp'&M).
  rewrite hstar_sep,hfstar_hempty_l in M.
  exists~ bp'.
Qed.

Lemma himpl_noduplicate2 : forall bp1 bp2 l1 l2,
\R[ \f[], bp1 ~b~> l1 \b* bp2 ~b~> l2] ==>
\R[ \f[noduplicates (bp1 :: bp2 :: nil)], bp1 ~b~> l1 \b* bp2 ~b~> l2].
Proof.
  intros. intros h (MA&MB). splits~.
  apply hf_empty_inv in MA. rewrite MA.
  apply hfpure_intro, noduplicates_two.
  intro N. rewrite N in MB.
  applys hbstar_hsingle_same_loc MB.
Qed.

Lemma hbstar_noduplicates3 : forall h p1 p2 p3 l1 l2 l3,
  (p1 ~b~> l1 \b* p2 ~b~> l2 \b* p3 ~b~> l3) (h `b) ->
  noduplicates (p1 :: p2 :: p3 :: nil).
Proof.
  introv M. rewrite listtoapp3.
  applys noduplicates_app.
  - applys noduplicates_two.
    lets N1 : hbstar_hsingle_same_loc p1.
    rewrite <- hbstar_assoc in M.
    destruct M as (hb1&hb2&M1&M).
    intro N. rewrite <- N in M1.
    apply N1 in M1. apply M1.
  - applys noduplicates_one.
  - intros p N1 N2.
    rewrite mem_cons_eq in N1.
    destruct N1.
    rewrite mem_one_eq in N2.
    subst. rewrite hbstar_comm in M.
    rewrite hbstar_assoc in M.
    destruct M as (hb1&hb2&M1&M2&M3).
    lets N1 : hbstar_hsingle_same_loc p3.
    apply N1 in M2. apply M2.
    rewrite mem_cons_eq in N2. destruct~ N2.
    rewrite mem_cons_eq in H. destruct~ H.
    subst. destruct M as (hb1&hb2&M1&M2&M3).
    lets N1 : hbstar_hsingle_same_loc p3.
    apply N1 in M2. apply M2.
    rewrite~ mem_nil_eq in H.
    rewrite~ mem_nil_eq in H0.
Qed.

Lemma himpl_noduplicate3 : forall bp1 bp2 bp3 l1 l2 l3,
\R[ \f[], bp1 ~b~> l1 \b* bp2 ~b~> l2 \b* bp3 ~b~> l3] ==>
\R[ \f[noduplicates (rev (bp3 :: bp2 :: bp1 :: nil))], 
    bp1 ~b~> l1 \b* bp2 ~b~> l2 \b* bp3 ~b~> l3].
Proof.
  intros. intros h (MA&MB). splits~.
  apply hf_empty_inv in MA. rewrite MA.
  applys hfpure_intro. applys hbstar_noduplicates3 MB.
Qed.

(*===========hforall=========*)
Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof. introv M. applys* M. Qed.

Lemma hforall_specialize : forall A (v:A) (J:A->hprop),
  (\forall x, J x) ==> (J v).
Proof. intros. intros h K. apply* K. Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_hforall_l : forall A (v:A) (J:A->hprop) H,
  J v ==> H ->
  (\forall x, J x) ==> H.
Proof. introv M. applys himpl_trans M. applys hforall_specialize. Qed.

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (\forall x, J x).
Proof. introv M. intros h K x. apply~ M. Qed.

(*-------------------magic wand---------------------------*)
Definition hwand (H1 H2:hprop) : hprop :=
  \exists H, H \* \[ (H1 \* H) ==> H2 ].

Notation "H1 \-* H2" := (hwand H1 H2) (at level 43, right associativity).

Lemma hwand_equiv : forall H H1 H2,
  (H ==> H1 \-* H2) <-> ((H1 \* H) ==> H2).
Proof.
  unfold hwand. iff M.
  - intros h.
    intros (h1&h2&NA&NB&NC&ND).
    apply M in NB.
    destruct NB as (H'&NB).
    rewrite hstar_comm in NB.
    apply hstar_hpure_iff in NB as (NB1&NB2).
    apply NB1. rewrite ND.
    applys~ hstar_intro.
  - intros h N.
    exists H.
    rewrite hstar_comm, hstar_hpure_iff.
    splits~.
Qed.

Lemma himpl_hwand_r : forall H0 H1 H2,
  (H1 \* H0) ==> H2 ->
  H0 ==> (H1 \-* H2).
Proof. introv M. applys hwand_equiv. applys M. Qed.

Lemma himpl_hwand_r_inv : forall H0 H1 H2,
  H0 ==> (H1 \-* H2) ->
  (H1 \* H0) ==> H2.
Proof. introv M. applys hwand_equiv. applys M. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof. intros. apply hwand_equiv. applys himpl_refl. Qed.

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof.
  introv M1 M2. applys himpl_hwand_r.
  eapply himpl_frame_l in M1.
  applys himpl_trans M1.
  applys himpl_trans hwand_cancel M2.
Qed.

Lemma hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).
Proof.
  intros. applys himpl_hwand_r. 
  rewrite <- hstar_assoc.
  applys himpl_trans himpl_frame_l hwand_cancel.
  applys hwand_cancel.
Qed.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof. intros. apply himpl_hwand_r. rewrite~ hstar_hempty_r. Qed.

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof.
  intros. applys himpl_hwand_r.
  rewrite <- hstar_assoc.
  applys himpl_frame_l hwand_cancel. 
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof.
  intros. applys himpl_antisym.
  { apply himpl_hwand_r. apply himpl_hwand_r.
    rewrite hstar_comm3.
    rewrite <- hstar_assoc.
    applys hwand_cancel. }
  { apply himpl_hwand_r.
    rewrite hstar_assoc. rewrite hstar_comm3, hstar_comm.
    applys himpl_trans himpl_frame_l.
    applys hwand_cancel.
    rewrite hstar_comm.
    applys hwand_cancel. }
Qed.

Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \-* H3) ==> (H2 \-* H3).
Proof.
  intros.
  applys hwand_equiv. rewrite hstar_comm3.
  rewrite <- hstar_assoc.
  applys hwand_cancel.
Qed.

Lemma hwand_refine : forall Hf1 Hf2 Hb1 Hb2,
  \R[Hf1 \f-* Hf2, Hb1 \b-* Hb2]
==>
  (\R[Hf1,Hb1] \-* \R[Hf2,Hb2]).
Proof.
  intros. intros h (MA&MB).
  destruct MA as (Hf0&MA).
  destruct MA as (hf1&hf2&A1&A2&A3&A4).
  apply hfpure_inv in A2 as [A21 A22].
  destruct MB as (HB0&MB).
  destruct MB as (hb1&hb2&B1&B2&B3&B4).
  apply hbpure_inv in B2 as [B21 B22].
  subst.
  rewrite union_empty_r in *.
  exists (\R[Hf0,HB0]).
  rewrite hstar_comm.
  rewrite hstar_hpure_iff.
  split~.
  intros h' T.
  rewrite hstar_sep in T.
  destruct T as [TA TB].
  splits*.
  rewrite state_get_eq.
  subst. splits~.
Qed.


(*--------  qwand ------------*)
Definition qwand (Q1 Q2:val->hprop) : hprop :=
  \forall v, (Q1 v) \-* (Q2 v).

Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43) : qwand_scope.

Open Scope qwand_scope.

Lemma qwand_specialize : forall (v:val) (Q1 Q2:val->hprop),
  (Q1 \--* Q2) ==> (Q1 v \-* Q2 v).
Proof.
  intros. unfold qwand.
  applys himpl_hforall_l v. apply himpl_refl.
Qed.

Lemma qwand_equiv : forall H Q1 Q2,
  H ==> (Q1 \--* Q2)  <->  (Q1 \*+ H) ===> Q2.
Proof.
  intros. iff M.
  { intros v. 
    applys himpl_trans.
    lets T : himpl_trans M (qwand_specialize v).
    applys himpl_frame_r T.
    applys hwand_cancel. }
  { applys himpl_hforall_r.
    intros v.
    applys himpl_hwand_r M. }
Qed.

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma hstar_qwand : forall Q1 Q2 H,
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof.
  intros. rewrite qwand_equiv.
  intros v.
  rewrite <- hstar_assoc.
  applys himpl_frame_l qwand_cancel.
Qed.

Lemma himpl_qwand_r : forall (Q1 Q2:val->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof. introv M. rewrite~ qwand_equiv. Qed.