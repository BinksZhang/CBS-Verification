(**

This file describes the representation and properties of inner-heap predicates.

Author: Bowen Zhang.

Date : 2021.07.24
*)

Set Implicit Arguments.
From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* CBS *) Require Export Language.

(*** =========== Definition of inner-heap predicates =====================  ***)

(** Core file-heap predicates, and their associated notations:
    - [\f[]] denotes the empty file-heap predicate
    - [\f[P]] denotes a pure file fact
    - [p ~f~> v] denotes a singleton file-heap
    - [H1 \f* H2] denotes the file-heap predicates separating conjunction
    - [\existsf x, H] denotes an existential (about file)
    - [\forallf x, H] denotes a universal (about file)
    - [ Hf \f-* Hf' ] denotes magic wand in file-heap predicates
*)

(** Core block-heap predicates, and their associated notations:
    - [\b[]] denotes the empty block-heap predicate
    - [\b[P]] denotes a pure block fact
    - [p ~b~> v] denotes a singleton block-heap
    - [H1 \b* H2] denotes the block-heap predicates separating conjunction
    - [\existsb x, H] denotes an existential (about block)
    - [\forallb x, H] denotes a universal (about block)
    - [ Hb \b-* Hb' ] denotes magic wand in block-heap predicates
*)

Definition hbprop := heapb -> Prop.
Definition hfprop := heapf -> Prop.

Implicit Types P : Prop.
Implicit Types Hb : hbprop.
Implicit Types Hf : hfprop.
Implicit Types Qb : val->hbprop.
Implicit Types Qf : val->hfprop.

(*** =============================================== ***)
Definition hbempty : hbprop :=
  fun h => (h = Fmap.empty).

Definition hfempty : hfprop :=
  fun h => (h = Fmap.empty).

Notation "\b[]" := (hbempty)
  (at level 0) : hprop_scope.
Notation "\f[]" := (hfempty)
  (at level 0) : hprop_scope.

(* singleton *)

Definition hbsingle (bp:bloc) (ll:list int) : hbprop :=
  fun h => (h = Fmap.single bp ll /\ bp <> bnull).

Definition hfsingle (fp:floc) (lb:list bloc) : hfprop :=
  fun h => (h = Fmap.single fp lb /\ fp <> fnull).

Notation "bp '~b~>' ll" := (hbsingle bp ll) (at level 32) : hprop_scope.
Notation "fp '~f~>' lb" := (hfsingle fp lb) (at level 32) : hprop_scope.

(* sep star *)

Definition hbstar (H1 H2 : hbprop) : hbprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hfstar (H1 H2 : hfprop) : hfprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Notation "H1 '\b*' H2" := (hbstar H1 H2)
  (at level 41, right associativity) : hprop_scope.
Notation "H1 '\f*' H2" := (hfstar H1 H2)
  (at level 41, right associativity) : hprop_scope.


Notation "Q \b*+ H" := (fun x => hbstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "Q \f*+ H" := (fun x => hfstar (Q x) H)
  (at level 40) : hprop_scope.

(* sep exists *)
Definition hbexists {A:Type} (J:A->hbprop) : hbprop :=
  fun h => exists x, J x h.

Definition hfexists {A:Type} (J:A->hfprop) : hfprop :=
  fun h => exists x, J x h.

Notation "'\existsb' x1 .. xn , H" :=
  (hbexists (fun x1 => .. (hbexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\existsb' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\existsf' x1 .. xn , H" :=
  (hfexists (fun x1 => .. (hfexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\existsf' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(* sep forall *)

Definition hbforall {A : Type} (J : A -> hbprop) : hbprop :=
  fun h => forall x, J x h.

Definition hfforall {A : Type} (J : A -> hfprop) : hfprop :=
  fun h => forall x, J x h.

Notation "'\forallb' x1 .. xn , H" :=
  (hbforall (fun x1 => .. (hbforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forallb' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forallf' x1 .. xn , H" :=
  (hfforall (fun x1 => .. (hfforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forallf' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(* sep pure *)
Open Scope hprop_scope.

Definition hbpure (P:Prop) : hbprop :=
  \existsb (p:P), \b[].

Definition hfpure (P:Prop) : hfprop :=
  \existsf (p:P), \f[].

Notation "\b[ P ]" := (hbpure P)
  (at level 0, format "\b[ P ]") : hprop_scope.

Notation "\f[ P ]" := (hfpure P)
  (at level 0, format "\f[ P ]") : hprop_scope.

(* ================================================================= *)
(** ** Basic properties of Inner-heap predicates operators *)

(* ----------------------------------------------------------------- *)
(** *** Tactic for automation *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.

(* ----------------------------------------------------------------- *)
(** the entailment relation *)

Definition hbimpl (H1 H2:hbprop) : Prop :=
  forall h, H1 h -> H2 h.
Definition hfimpl (H1 H2:hfprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 =b=> H2" := (hbimpl H1 H2) (at level 55) : hprop_scope.
Notation "H1 =f=> H2" := (hfimpl H1 H2) (at level 55) : hprop_scope.

Definition qbimpl {A} (Q1 Q2:A->hbprop) : Prop :=
  forall (v:A), Q1 v =b=> Q2 v.
Definition qfimpl {A} (Q1 Q2:A->hfprop) : Prop :=
  forall (v:A), Q1 v =f=> Q2 v.

Notation "Q1 =b==> Q2" := (qbimpl Q1 Q2) (at level 55) : hprop_scope.
Notation "Q1 =f==> Q2" := (qfimpl Q1 Q2) (at level 55) : hprop_scope.

(*------------magic wand---------------*)
Definition hbwand (Hb1 Hb2:hbprop) : hbprop :=
  \existsb (Hb0:hbprop), Hb0 \b* \b[(Hb1 \b* Hb0) =b=> Hb2].

Definition hfwand (Hf1 Hf2:hfprop) : hfprop :=
  \existsf (Hf0:hfprop), Hf0 \f* \f[(Hf1 \f* Hf0) =f=> Hf2].

Notation "H1 \b-* H2" := (hbwand H1 H2) (at level 43, right associativity).
Notation "H1 \f-* H2" := (hfwand H1 H2) (at level 43, right associativity).


Definition qfwand (Q1 Q2:val->hfprop) : hfprop :=
  \existsf H0, H0 \f* \f[ Q1 \f*+ H0 =f==> Q2 ].

Definition qbwand (Q1 Q2:val->hbprop) : hbprop :=
  \existsb H0, H0 \b* \b[ Q1 \b*+ H0 =b==> Q2 ].

Notation "Q1 \f--* Q2" := (qfwand Q1 Q2) (at level 43).
Notation "Q1 \b--* Q2" := (qbwand Q1 Q2) (at level 43).

(*------the order relation in the set of inner-heap predicate--------*)
(* refl *)
Lemma hbimpl_refl : forall H,
  H =b=> H.
Proof using. introv M. auto. Qed.

Lemma hfimpl_refl : forall H,
  H =f=> H.
Proof using. introv M. auto. Qed.

Hint Resolve hbimpl_refl.
Hint Resolve hfimpl_refl.

(* trans *)

Lemma hbimpl_trans : forall H2 H1 H3,
  (H1 =b=> H2) ->
  (H2 =b=> H3) ->
  (H1 =b=> H3).
Proof using. introv M1 M2. unfolds* hbimpl. Qed.

Lemma hfimpl_trans : forall H2 H1 H3,
  (H1 =f=> H2) ->
  (H2 =f=> H3) ->
  (H1 =f=> H3).
Proof using. introv M1 M2. unfolds* hfimpl. Qed.

Lemma hbimpl_trans_r : forall H2 H1 H3,
   H2 =b=> H3 ->
   H1 =b=> H2 ->
   H1 =b=> H3.
Proof using. introv M1 M2. applys* hbimpl_trans M2 M1. Qed.

Lemma hfimpl_trans_r : forall H2 H1 H3,
   H2 =f=> H3 ->
   H1 =f=> H2 ->
   H1 =f=> H3.
Proof using. introv M1 M2. applys* hfimpl_trans M2 M1. Qed.

(* antisym *)

Lemma hbimpl_antisym : forall H1 H2,
  (H1 =b=> H2) ->
  (H2 =b=> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hfimpl_antisym : forall H1 H2,
  (H1 =f=> H2) ->
  (H2 =f=> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hbprop_op_comm : forall (op:hbprop->hbprop->hbprop),
  (forall H1 H2, op H1 H2 =b=> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys hbimpl_antisym; applys M. Qed.

Lemma hfprop_op_comm : forall (op:hfprop->hfprop->hfprop),
  (forall H1 H2, op H1 H2 =f=> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys hfimpl_antisym; applys M. Qed.

Lemma qbimpl_refl : forall A (Q:A->hbprop),
   Q =b==> Q.
Proof using. intros. unfolds*. Qed.

Lemma qfimpl_refl : forall A (Q:A->hfprop),
   Q =f==> Q.
Proof using. intros. unfolds*. Qed.

Hint Resolve qbimpl_refl.
Hint Resolve qfimpl_refl.

(*++++++++++ Some properties +++++++++++++*)
(* ----------------------------------------------------------------- *)
(** *** Properties of [hempty] *)

Lemma hb_empty_intro :
  \b[] hb_empty.
Proof using. unfolds*. Qed.

Lemma hb_empty_inv : forall h,
  \b[] h ->
  h = hb_empty.
Proof using. auto. Qed.

Lemma hf_empty_intro :
  \f[] hf_empty.
Proof using. unfolds*. Qed.

Lemma hf_empty_inv : forall h,
  \f[] h ->
  h = hf_empty.
Proof using. auto. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hstar] *)

Lemma hbstar_intro : forall (H1 H2:hbprop) h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \b* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hbstar_inv : forall H1 H2 h,
  (H1 \b* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hfstar_intro : forall (H1 H2:hfprop) h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \f* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hfstar_inv : forall H1 H2 h,
  (H1 \f* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hbstar_comm : forall H1 H2,
   H1 \b* H2 = H2 \b* H1.
Proof using.
  applys hbprop_op_comm. unfold hbprop, hbstar. intros H1 H2.
  intros h (h1&h2&M1&M2&D&U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hfstar_comm : forall H1 H2,
   H1 \f* H2 = H2 \f* H1.
Proof using.
  applys hfprop_op_comm. unfold hbprop, hfstar. intros H1 H2.
  intros h (h1&h2&M1&M2&D&U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hbstar_assoc : forall H1 H2 H3,
  (H1 \b* H2) \b* H3 = H1 \b* (H2 \b* H3).
Proof using.
  intros H1 H2 H3. applys hbimpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hbstar_intro. } rewrite~ union_assoc in U. }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hbstar_intro. } rewrite <- union_assoc in U. auto. }
Qed.

Lemma hfstar_assoc : forall H1 H2 H3,
  (H1 \f* H2) \f* H3 = H1 \f* (H2 \f* H3).
Proof using.
  intros H1 H2 H3. applys hfimpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hfstar_intro. } rewrite~ union_assoc in U. }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hfstar_intro. } rewrite <- union_assoc in U. auto. }
Qed.

Lemma hbstar_hempty_l : forall H,
  \b[] \b* H = H.
Proof using.
  intros. applys hbimpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). forwards E: hb_empty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists hb_empty h. splits~. { applys hb_empty_intro. } rewrite~ union_empty_l. }
Qed.

Lemma hfstar_hempty_l : forall H,
  \f[] \f* H = H.
Proof using.
  intros. applys hfimpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). forwards E: hf_empty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists hf_empty h. splits~. { applys hf_empty_intro. } rewrite~ union_empty_l. }
Qed.

Lemma hbstar_hempty_r : forall (H:hbprop),
  H \b* \b[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hbstar_comm. applys~ hbstar_hempty_l.
Qed.

Lemma hfstar_hempty_r : forall (H:hfprop),
  H \f* \f[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hfstar_comm. applys~ hfstar_hempty_l.
Qed.

Lemma hbimpl_frame_l : forall (H2 H1 H1':hbprop) ,
  H1 =b=> H1' ->
  (H1 \b* H2) =b=> (H1' \b* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma hfimpl_frame_l : forall (H2 H1 H1':hfprop) ,
  H1 =f=> H1' ->
  (H1 \f* H2) =f=> (H1' \f* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma hbimpl_frame_r : forall H1 H2 H2',
  H2 =b=> H2' ->
  (H1 \b* H2) =b=> (H1 \b* H2').
Proof using.
  introv M. do 2 rewrite (@hbstar_comm H1). applys~ hbimpl_frame_l.
Qed.

Lemma hfimpl_frame_r : forall H1 H2 H2',
  H2 =f=> H2' ->
  (H1 \f* H2) =f=> (H1 \f* H2').
Proof using.
  introv M. do 2 rewrite (@hfstar_comm H1). applys~ hfimpl_frame_l.
Qed.

Lemma hbimpl_frame_lr : forall H1 H1' H2 H2',
  H1 =b=> H1' ->
  H2 =b=> H2' ->
  (H1 \b* H2) =b=> (H1' \b* H2').
Proof using.
  introv M1 M2. applys hbimpl_trans. applys~ hbimpl_frame_l M1. applys~ hbimpl_frame_r.
Qed.

Lemma hfimpl_frame_lr : forall H1 H1' H2 H2',
  H1 =f=> H1' ->
  H2 =f=> H2' ->
  (H1 \f* H2) =f=> (H1' \f* H2').
Proof using.
  introv M1 M2. applys hfimpl_trans. applys~ hfimpl_frame_l M1. applys~ hfimpl_frame_r.
Qed. 

Lemma hbimpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 =b=> H2 ->
  H2 \b* H3 =b=> H4 ->
  H1 \b* H3 =b=> H4.
Proof using.
  introv M1 M2. applys hbimpl_trans M2. applys hbimpl_frame_l M1.
Qed.

Lemma hfimpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 =f=> H2 ->
  H2 \f* H3 =f=> H4 ->
  H1 \f* H3 =f=> H4.
Proof using.
  introv M1 M2. applys hfimpl_trans M2. applys hfimpl_frame_l M1.
Qed.

Lemma hbimpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 =b=> H2 ->
  H3 \b* H2 =b=> H4 ->
  H3 \b* H1 =b=> H4.
Proof using.
  introv M1 M2. applys hbimpl_trans M2. applys hbimpl_frame_r M1.
Qed.

Lemma hfimpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 =f=> H2 ->
  H3 \f* H2 =f=> H4 ->
  H3 \f* H1 =f=> H4.
Proof using.
  introv M1 M2. applys hfimpl_trans M2. applys hfimpl_frame_r M1.
Qed.

Lemma hbstar_hexists : forall A (J:A->hbprop) H,
  (hbexists J) \b* H = hbexists (fun x => (J x) \b* H).
Proof using.
  intros. applys hbimpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hfstar_hexists : forall A (J:A->hfprop) H,
  (hfexists J) \f* H = hfexists (fun x => (J x) \f* H).
Proof using.
  intros. applys hfimpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
Qed.

Lemma hbstar_hforall : forall H A (J:A->hbprop),
  (hbforall J) \b* H =b=> hbforall (J \b*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma hfstar_hforall : forall H A (J:A->hfprop),
  (hfforall J) \f* H =f=> hfforall (J \f*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.


(* ----------------------------------------------------------------- *)
(** ***  Properties of [hpure] *)

Lemma hbpure_intro : forall P,
  P ->
  \b[P] hb_empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hfpure_intro : forall P,
  P ->
  \f[P] hf_empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hbpure_inv : forall P h,
  \b[P] h ->
  P /\ h = hb_empty.
Proof using. introv (p&M). split~. Qed.

Lemma hfpure_inv : forall P h,
  \f[P] h ->
  P /\ h = hf_empty.
Proof using. introv (p&M). split~. Qed.

Lemma hbstar_hpure : forall P H h,
  (\b[P] \b* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hbpure.
  rewrite hbstar_hexists. rewrite* hbstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hfstar_hpure : forall P H h,
  (\f[P] \f* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hfpure.
  rewrite hfstar_hexists. rewrite* hfstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hbstar_hpure_iff : forall P H h,
  (\b[P] \b* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hbstar_hpure. Qed.

Lemma hfstar_hpure_iff : forall P H h,
  (\f[P] \f* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hfstar_hpure. Qed.

Lemma hbimpl_hstar_hpure_r : forall P H H',
  P ->
  (H =b=> H') ->
  H =b=> (\b[P] \b* H').
Proof using. introv HP W. intros h K. rewrite* hbstar_hpure. Qed.

Lemma hfimpl_hstar_hpure_r : forall P H H',
  P ->
  (H =f=> H') ->
  H =f=> (\f[P] \f* H').
Proof using. introv HP W. intros h K. rewrite* hfstar_hpure. Qed.

Lemma hbpure_inv_hempty : forall P h,
  \b[P] h ->
  P /\ \b[] h.
Proof using.
  introv M. rewrite <- hbstar_hpure. rewrite~ hbstar_hempty_r.
Qed.

Lemma hfpure_inv_hempty : forall P h,
  \f[P] h ->
  P /\ \f[] h.
Proof using.
  introv M. rewrite <- hfstar_hpure. rewrite~ hfstar_hempty_r.
Qed.

Lemma hbpure_intro_hempty : forall P h,
  \b[] h ->
  P ->
  \b[P] h.
Proof using.
  introv M N. rewrite <- (hbstar_hempty_l \b[P]).
  rewrite hbstar_comm. rewrite~ hbstar_hpure.
Qed.

Lemma hfpure_intro_hempty : forall P h,
  \f[] h ->
  P ->
  \f[P] h.
Proof using.
  introv M N. rewrite <- (hfstar_hempty_l \f[P]).
  rewrite hfstar_comm. rewrite~ hfstar_hpure.
Qed.

Lemma hbimpl_hempty_hpure : forall P,
  P ->
  \b[] =b=> \b[P].
Proof using. introv HP. intros h Hh. applys* hbpure_intro_hempty. Qed.

Lemma hfimpl_hempty_hpure : forall P,
  P ->
  \f[] =f=> \f[P].
Proof using. introv HP. intros h Hh. applys* hfpure_intro_hempty. Qed.

Lemma hbimpl_hstar_hpure_l : forall P H H',
  (P -> H =b=> H') ->
  (\b[P] \b* H) =b=> H'.
Proof using.
  introv W Hh. rewrite hbstar_hpure in Hh. applys* W.
Qed.

Lemma hfimpl_hstar_hpure_l : forall P H H',
  (P -> H =f=> H') ->
  (\f[P] \f* H) =f=> H'.
Proof using.
  introv W Hh. rewrite hfstar_hpure in Hh. applys* W.
Qed.

Lemma hbempty_eq_hpure_true :
  \b[] = \b[True].
Proof using.
  applys hbimpl_antisym; intros h M.
  { applys* hbpure_intro_hempty. }
  { forwards*: hbpure_inv_hempty M. }
Qed.

Lemma hfempty_eq_hpure_true :
  \f[] = \f[True].
Proof using.
  applys hfimpl_antisym; intros h M.
  { applys* hfpure_intro_hempty. }
  { forwards*: hfpure_inv_hempty M. }
Qed.

Lemma hbfalse_hstar_any : forall H,
  \b[False] \b* H = \b[False].
Proof using.
  intros. applys hbimpl_antisym; intros h; rewrite hbstar_hpure; intros M.
  { false*. } { lets: hbpure_inv_hempty M. false*. }
Qed.

Lemma hffalse_hstar_any : forall H,
  \f[False] \f* H = \f[False].
Proof using.
  intros. applys hfimpl_antisym; intros h; rewrite hfstar_hpure; intros M.
  { false*. } { lets: hfpure_inv_hempty M. false*. }
Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hexists] *)

Lemma hbexists_intro : forall A (x:A) (J:A->hbprop) h,
  J x h ->
  (hbexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hfexists_intro : forall A (x:A) (J:A->hfprop) h,
  J x h ->
  (hfexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hbexists_inv : forall A (J:A->hbprop) h,
  (hbexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma hfexists_inv : forall A (J:A->hfprop) h,
  (hfexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma hbimpl_hexists_l : forall A H (J:A->hbprop),
  (forall x, J x =b=> H) ->
  (hbexists J) =b=> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma hbimpl_hexists_r : forall A (x:A) H J,
  (H =b=> J x) ->
  H =b=> (hbexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma hfimpl_hexists_l : forall A H (J:A->hfprop),
  (forall x, J x =f=> H) ->
  (hfexists J) =f=> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma hfimpl_hexists_r : forall A (x:A) H J,
  (H =f=> J x) ->
  H =f=> (hfexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hforall] *)

Lemma hbforall_intro : forall A (J:A->hbprop) h,
  (forall x, J x h) ->
  (hbforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hfforall_intro : forall A (J:A->hfprop) h,
  (forall x, J x h) ->
  (hfforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hbforall_inv : forall A (J:A->hbprop) h,
  (hbforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma hfforall_inv : forall A (J:A->hfprop) h,
  (hfforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma hbimpl_hforall_r : forall A (J:A->hbprop) H,
  (forall x, H =b=> J x) ->
  H =b=> (hbforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma hbimpl_hforall_l : forall A x (J:A->hbprop) H,
  (J x =b=> H) ->
  (hbforall J) =b=> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hfimpl_hforall_r : forall A (J:A->hfprop) H,
  (forall x, H =f=> J x) ->
  H =f=> (hfforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma hfimpl_hforall_l : forall A x (J:A->hfprop) H,
  (J x =f=> H) ->
  (hfforall J) =f=> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hbforall_specialize : forall A (x:A) (J:A->hbprop),
  (hbforall J) =b=> (J x).
Proof using. intros. applys* hbimpl_hforall_l x. Qed.

Lemma hfforall_specialize : forall A (x:A) (J:A->hfprop),
  (hfforall J) =f=> (J x).
Proof using. intros. applys* hfimpl_hforall_l x. Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [hsingle] *)

Lemma hbsingle_intro : forall p (v:list int),
  p <> bnull ->
  (p ~b~> v) (Fmap.single p v).
Proof using. introv N. hnfs*. Qed.

Lemma hfsingle_intro : forall p (v:list bloc),
  p <> fnull ->
  (p ~f~> v) (Fmap.single p v).
Proof using. introv N. hnfs*. Qed.

Lemma hfsingle_inv: forall p (v:list bloc) h,
  (p ~f~> v) h ->
  h = Fmap.single p v /\ p <> fnull.
Proof using. auto. Qed.

Lemma hbsingle_inv: forall p (v:list int) h,
  (p ~b~> v) h ->
  h = Fmap.single p v /\ p <> bnull.
Proof using. auto. Qed.

Lemma hbsingle_not_null : forall p (v:list int),
  (p ~b~> v) =b=> (p ~b~> v) \b* \b[p <> bnull].
Proof using.
  introv. intros h (K&N). rewrite hbstar_comm, hbstar_hpure.
  split*. subst. applys* hbsingle_intro.
Qed.

Lemma hfsingle_not_null : forall p (v:list bloc),
  (p ~f~> v) =f=> (p ~f~> v) \f* \f[p <> fnull].
Proof using.
  introv. intros h (K&N). rewrite hfstar_comm, hfstar_hpure.
  split*. subst. applys* hfsingle_intro.
Qed.

Lemma hbstar_hsingle_same_loc : forall p (v1 v2:list int),
  (p ~b~> v1) \b* (p ~b~> v2) =b=> \b[False].
Proof using.
  intros. unfold hbsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Lemma hfstar_hsingle_same_loc : forall p (v1 v2:list bloc),
  (p ~f~> v1) \f* (p ~f~> v2) =f=> \f[False].
Proof using.
  intros. unfold hfsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.
Arguments hbstar_hsingle_same_loc : clear implicits.
Arguments hfstar_hsingle_same_loc : clear implicits.


(*-------------------Properties of magic wand-----------------------*)
Lemma hfwand_equiv : forall Hf0 Hf1 Hf2,
  (Hf0 =f=> Hf1 \f-* Hf2) <-> (Hf1 \f* Hf0 =f=> Hf2).
Proof using.
  unfold hfwand. iff M.
  - intros h.
    intros (h1&h2&NA&NB&NC&ND).
    apply M in NB.
    destruct NB as (Hf&NB).
    rewrite hfstar_comm in NB.
    apply hfstar_hpure_iff in NB as (NB1&NB2).
    apply NB1. rewrite ND.
    applys~ hfstar_intro.
  - intros h N.
    exists Hf0.
    rewrite hfstar_comm, hfstar_hpure_iff.
    splits~.
Qed.

Lemma hbwand_equiv : forall Hb0 Hb1 Hb2,
  (Hb0 =b=> Hb1 \b-* Hb2) <-> (Hb1 \b* Hb0 =b=> Hb2).
Proof using.
  unfold hfwand. iff M.
  - intros h.
    intros (h1&h2&NA&NB&NC&ND).
    apply M in NB.
    destruct NB as (Hf&NB).
    rewrite hbstar_comm in NB.
    apply hbstar_hpure_iff in NB as (NB1&NB2).
    apply NB1. rewrite ND.
    applys~ hbstar_intro.
  - intros h N.
    exists Hb0.
    rewrite hbstar_comm, hbstar_hpure_iff.
    splits~.
Qed.

Lemma hfimpl_hwand_r : forall Hf0 Hf1 Hf2,
  (Hf1 \f* Hf0) =f=> Hf2 ->
  Hf0 =f=> (Hf1 \f-* Hf2).
Proof.
  introv M. applys hfwand_equiv. applys M.
Qed.

Lemma hbimpl_hwand_r : forall Hb0 Hb1 Hb2,
  (Hb1 \b* Hb0) =b=> Hb2 ->
  Hb0 =b=> (Hb1 \b-* Hb2).
Proof.
  introv M. applys hbwand_equiv. applys M.
Qed.

Lemma hfimpl_hwand_r_inv : forall Hf0 Hf1 Hf2,
  Hf0 =f=> (Hf1 \f-* Hf2) ->
  (Hf1 \f* Hf0) =f=> Hf2.
Proof. introv M. applys hfwand_equiv. applys M. Qed.

Lemma hbimpl_hwand_r_inv : forall Hb0 Hb1 Hb2,
  Hb0 =b=> (Hb1 \b-* Hb2) ->
  (Hb1 \b* Hb0) =b=> Hb2.
Proof. introv M. applys hbwand_equiv. applys M. Qed.

Lemma hfwand_cancel : forall Hf1 Hf2,
  Hf1 \f* (Hf1 \f-* Hf2) =f=> Hf2.
Proof. intros. applys hfimpl_hwand_r_inv. applys hfimpl_refl. Qed.

Lemma hbwand_cancel : forall Hb1 Hb2,
  Hb1 \b* (Hb1 \b-* Hb2) =b=> Hb2.
Proof. intros. applys hbimpl_hwand_r_inv. applys hbimpl_refl. Qed.

Arguments hfwand_cancel : clear implicits.
Arguments hbwand_cancel : clear implicits.

Lemma qfwand_equiv : forall Hf Q1 Q2,
  Hf =f=> (Q1 \f--* Q2)  <->  (Q1 \f*+ Hf) =f==> Q2.
Proof.
  unfold qfwand. iff M.
  - intros v h.
    intros (h1&h2&NA&NB&NC&ND).
    apply M in NB.
    destruct NB as (Hf'&NB).
    rewrite hfstar_comm in NB.
    apply hfstar_hpure_iff in NB as (NB1&NB2).
    apply NB1. rewrite ND.
    applys~ hfstar_intro.
  - intros h N.
    exists Hf.
    rewrite hfstar_comm, hfstar_hpure_iff.
    splits~.
Qed.

Lemma qbwand_equiv : forall Hb Q1 Q2,
  Hb =b=> (Q1 \b--* Q2)  <->  (Q1 \b*+ Hb) =b==> Q2.
Proof.
  unfold qbwand. iff M.
  - intros v h.
    intros (h1&h2&NA&NB&NC&ND).
    apply M in NB.
    destruct NB as (Hf'&NB).
    rewrite hbstar_comm in NB.
    apply hbstar_hpure_iff in NB as (NB1&NB2).
    apply NB1. rewrite ND.
    applys~ hbstar_intro.
  - intros h N.
    exists Hb.
    rewrite hbstar_comm, hbstar_hpure_iff.
    splits~.
Qed.

Lemma qfwand_cancel : forall Q1 Q2,
  Q1 \f*+ (Q1 \f--* Q2) =f==> Q2.
Proof. intros. rewrite <- qfwand_equiv. applys qfimpl_refl. Qed.

Lemma qbwand_cancel : forall Q1 Q2,
  Q1 \b*+ (Q1 \b--* Q2) =b==> Q2.
Proof. intros. rewrite <- qbwand_equiv. applys qbimpl_refl. Qed.

Lemma qfwand_specialize : forall (v:val) (Q1 Q2:val->hfprop),
  (Q1 \f--* Q2) =f=> (Q1 v \f-* Q2 v).
Proof.
  intros. unfold qfwand, hfwand.
  intros h M.
  destruct M as (Hf&M).
  rewrite hfstar_comm in M.
  apply hfstar_hpure_iff in M as (MA&MB).
  exists Hf.
  rewrite hfstar_comm, hfstar_hpure_iff.
  splits~.
Qed.

Lemma qbwand_specialize : forall (v:val) (Q1 Q2:val->hbprop),
  (Q1 \b--* Q2) =b=> (Q1 v \b-* Q2 v).
Proof.
  intros. unfold qbwand, hbwand.
  intros h M.
  destruct M as (Hb&M).
  rewrite hbstar_comm in M.
  apply hbstar_hpure_iff in M as (MA&MB).
  exists Hb.
  rewrite hbstar_comm, hbstar_hpure_iff.
  splits~.
Qed.