(** 
This file describes the construction of our proof system, mainly about:
  1. The definitions of Separation Logic triple in CBS:
    a. three different definitions of CBS-SL-triple
    b. prove the equivalence of three definitions
  2. how to state and prove the reasoning rules of:
    a. primitive operations (block & file)
    b. terms
    c. structural rules
  (we can prove the SL rules by the proven Hoare rules ).

Author: Bowen Zhang.

Date : 2023.02.22
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* CBS *) Require Export Himpl Hoare.

(* ################################################################# *)

(*** Implicit Types (to improve the readability) ***)

Implicit Types b bp : bloc.
Implicit Types f fp: floc.
Implicit Types ln : list int.
Implicit Types n : int.
Implicit Types v : val.
Implicit Types t : trm.
Implicit Types be : bool.
Implicit Types hb : heapb.
Implicit Types sb : stateb.
Implicit Types hf : heapf.
Implicit Types sf : statef.

(*all operators have opaque definitions*)
Global Opaque hbempty hbpure hbstar hbsingle hbexists hbforall.
Global Opaque hfempty hfpure hfstar hfsingle hfexists hfforall.

(* ################################################################# *)
Open Scope liblist_scope.
Open Scope Z_scope.

(* ================================================================================ *)
(** ** Separation Logic Formal System for CBS ** **)

(**============= * Definition of Separation Logic triple ================*)
(* 1st way: using refinement predicate *)
Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
forall Hf Hb,
    hoare t (H \* \R[Hf,Hb]) (Q \*+ \R[Hf,Hb]).

(* 2nd way: using CBS predicate *)
Definition triple_pred (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
forall H',
    hoare t (H \* H') (Q \*+ H').

(* 3rd way: using CBS heap *)
Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
forall h1 h2,
  glodisjoint h1 h2 ->
  H h1 ->
  exists h1' v,
       glodisjoint h1' h2
    /\ eval (h1 \g h2) t (h1' \g h2) v
    /\ Q v h1'.

(* 1st definition <-> 2nd definition *)
Definition triple_iff_triple_pred: forall t H Q,
  triple_pred t H Q  <->  triple t H Q.
Proof.
  intros. unfolds~ triple_pred,triple. iff* R.
  intros H'. lets M : refine_eq' H'. rewrite M.
  intros hf hb (h1&h2&KA&(hf1&hb1&h11&h12&KB1&KB2&KB3&KB4)&KC&KD).
  lets T : R (= hf1) (= hb1) hf hb.
  apply hpure_inv in KB1 as (KB11&KB12).
  subst. unfold glounion in KD.
  simpls. do 2 rewrite union_empty_l in KD.
  lets C : hstar_intro KA KB2 KC.
  unfold glounion in C. rewrite <- KD in C.
  apply T in C as (hf'&hb'&v&CA&CB).
  exists hf' hb' v. splits~.
  destruct CB as (h3&h4&C1&C2&C3&C4).
  exists~ h3 h4. splits~.
  exists~ hf1 hb1. rewrite hstar_hpure_iff.
  splits~.
Qed.

(* 2nd definition <-> 3rd definition *)
Lemma triple_pred_iff_triple_lowlevel : forall t H Q,
  triple_pred t H Q <-> triple_lowlevel t H Q.
Proof using.
  unfold triple_pred,triple_lowlevel. iff* M.
  - introv D P1. unfold hoare in M.
    forwards~ (hf'&hb'&v&R1&R2):
      (rm M) (=h2) ((fst h1) \u (fst h2)) ((snd h1) \u (snd h2)).
    exists~ h1 h2.
    destruct R2 as (h1'&h2'&HA&HB&HC&HD).
    subst. exists~ h1' v. splits~.
    rewrite HD in R1. apply R1.
  - introv (h1&h2&HA&HB&HC&HD).
    forwards* (h1'&v&MC&MD&ME) : (rm M) h1 h2.
    exists ((fst h1') \u (fst h2)) ((snd h1') \u (snd h2)) v.
    rewrite HD. split~.  apply* hstar_intro.
Qed.

(**====================  separation logic rule  ===========================**)

(*------------------ SL rule: block prim operations---------------*)
Lemma triple_bcreate : forall Hf ln,
  triple (bprim_create (val_listint ln))
    (\R[ Hf, \b[] ])
    (fun r => \exists b, \[r= (val_bloc b)] \* (\R[ Hf, (b ~b~> ln)]) ).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bcreate hstar_sep_l.

  intros r h M.
  destruct M as (b&M).
  apply hstar_hpure_iff in M as [M1 M].
  destruct M as (MA&MB). 
  rewrite hstar_hexists. exists b.
  rewrite hstar_assoc, hstar_hpure. splits~.
  rewrite hstar_sep, state_get_eq.
  splits~. simpls.
  rewrite hbstar_hempty_l in MB. auto.
Qed.

Lemma triple_bget: forall Hf b ln,
  triple (bprim_get b)
    (\R[ Hf, (b ~b~> ln)])
    (fun r => \[r=(val_listint ln)] \* (\R[ Hf, (b ~b~> ln)])).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bget hstar_sep_l.
  intros r h R.
  apply hstar_hpure_iff in R as [R1 R].
  destruct R as (HA&HB).
  rewrite hstar_assoc, hstar_hpure. splits~.
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_bdelete: forall Hf b ln,
  triple (bprim_delete b)
    (\R[ Hf, (b ~b~> ln)])
    (fun _ =>(\R[ Hf, \b[]])).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bdelete hstar_sep_l.
  intros r h R.
  apply hstar_hpure_iff in R as [R1 R].
  destruct R as (HA&HB).
  rewrite hstar_sep, state_get_eq.
  splits~. simpls. rewrite~ hbstar_hempty_l.
Qed.

Lemma triple_bappend : forall Hf b ln1 ln2,
  triple (bprim_append b (val_listint ln2))
    ( \R[Hf, (b ~b~> ln1)] )
    (fun _ => \R[Hf, b ~b~> (ln1++ln2)]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bappend.
  rewrite hstar_sep. apply himpl_refl.
  intros r h (RA&RB).
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_btruncate : forall Hf b l n,
  triple (bprim_trun b n)
    ( \R[Hf, (b ~b~> l)] )
    (fun _ => \R[Hf, b ~b~> (droplast (to_nat n) l)]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_btruncate.
  rewrite hstar_sep. apply himpl_refl.
  intros r h (RA&RB).
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_bsize : forall Hf b ln1,
  triple (bprim_size b )
    ( \R[Hf, (b ~b~> ln1)] )
    (fun r => \[r = List.length ln1] \* \R[Hf, (b ~b~> ln1)]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bsize.
  rewrite hstar_sep. apply himpl_refl.
  intros r h R.
  rewrite hstar_hpure_iff in R.
  destruct R as (RA&RB).
  rewrite hstar_assoc. rewrite hstar_hpure.
  splits~. rewrite~ hstar_sep.
Qed.

(*-------------------- SL rule: file prim operations -------------------*)
Lemma triple_fcreate : forall Hb lb,
  triple (fprim_create (val_listbloc lb))
    (\R[ \f[], Hb ])
    (fun r => \exists f, \[r = val_floc f] \* \R[(f ~f~> lb), Hb ]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fcreate hstar_sep_l.
  introv (f&M).
  apply hstar_hpure_iff in M as (M1&(MA&MB)).
  rewrite hstar_hexists. exists f.
  rewrite hstar_assoc, hstar_hpure. splits~.
  rewrite hstar_sep. splits~.
Qed.

Lemma triple_fget: forall Hb (f:floc) lb,
  triple (fprim_get f)
    (\R[ (f ~f~> lb), Hb])
    (fun r =>\[r=(val_listbloc lb)] \* \R[(f ~f~> lb), Hb]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fget hstar_sep_l.
  intros r h M.
  apply hstar_hpure_iff in M as (MA&(M1&M2)).
  rewrite hstar_assoc, hstar_hpure. splits~.
  rewrite hstar_sep. splits~.
Qed.

Lemma triple_fget_nth_blk : forall Hb f lb n,
  triple (fprim_nthblk f n)
    (\R[ f ~f~> lb, Hb ])
    (fun r => \[r = val_bloc (nth_default bnull (Z.to_nat n) lb)] \* 
              \R[(f ~f~> lb),Hb ]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fget_nth_blk hstar_sep_l.
  intros r h M.
  apply hstar_hpure_iff in M as [MA M].
  destruct M as (M1&M2).
  rewrite hstar_assoc, hstar_hpure. splits~.
  rewrite hstar_sep, state_get_eq. splits~.
Qed.

Lemma triple_fset_nth_blk : forall Hb f lb n b,
  triple (fprim_set f n b)
    (\R[ f ~f~> lb, Hb ])
    (fun r => \R[ (f ~f~> (LibList.update (Z.to_nat n) b lb)), Hb ]).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fset_nth_blk hstar_sep_l.
  intros r h M.
  destruct M as (M1&M2).
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_fdelete: forall Hb f lb,
  triple (fprim_delete f)
    (\R[ (f ~f~> lb), Hb])
    (fun r =>(\R[ \f[], Hb])).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fdelete hstar_sep_l.
  intros r h M.
  apply hstar_hpure_iff in M as [MA M].
  destruct M as (M1&M2).
  rewrite hstar_sep, state_get_eq.
  splits~. simpl.
  rewrite~ hfstar_hempty_l.
Qed.

Lemma triple_fattach: forall Hb f lb1 lb2,
  triple (fprim_attach f (val_listbloc lb2))
    ( \R[(f ~f~> lb1), Hb] )
    (fun r =>(\R[(f ~f~> (lb1++lb2)), Hb])).
Proof.
  intros. intros Hf' Hb'.
  applys hoare_conseq hoare_fattach.
  rewrite hstar_sep, hfstar_hempty_l.
  apply himpl_refl.
  intros r. rewrite hstar_sep. apply himpl_refl.
Qed.

Lemma triple_ftrun : forall Hb f lb n,
  triple (fprim_trun f n)
    ( \R[ (f ~f~> lb), Hb] )
    (fun _ => \R[f ~f~> (droplast (to_nat n) lb), Hb]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_ftruncate.
  rewrite hstar_sep. apply himpl_refl.
  intros r h (RA&RB).
  rewrite hstar_sep, state_get_eq.
  splits~.
Qed.

Lemma triple_fsize : forall Hb f lb,
  triple (fprim_size f )
    ( \R[(f ~f~> lb), Hb] )
    (fun r => \[r = List.length lb] \* \R[(f ~f~> lb), Hb]).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_fsize.
  rewrite hstar_sep. apply himpl_refl.
  intros r h R.
  rewrite hstar_hpure_iff in R.
  destruct R as (RA&RB).
  rewrite hstar_assoc. rewrite hstar_hpure.
  splits~. rewrite~ hstar_sep.
Qed.


(* -------------------- SL rule: aux prim operations------------------ *)

Lemma triple_add : forall H n1 n2,
  triple (val_add n1 n2) H
    (fun r => (\[r = (n1 + n2)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (n1+n2).
  splits~. apply eval_add.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_min : forall H n1 n2,
  triple (val_min n1 n2) H
    (fun r => (\[r = (n1 - n2)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (n1-n2).
  splits~. apply eval_min.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_eq : forall H n1 n2,
  triple (val_eq n1 n2) H
    (fun r => (\[r = val_bool (n1 =? n2)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_bool (n1 =? n2)).
  splits~. apply eval_eq.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_le : forall H n1 n2,
  triple (val_le n1 n2) H
    (fun r => (\[r = (val_bool (isTrue (n1 <= n2)))] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_bool (isTrue (n1 <= n2))). splits.
  apply eval_le.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_rev : forall H ln1,
  triple (val_list_rev (val_listint ln1)) H
    (fun r => (\[r = val_listint (rev ln1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (rev ln1)).
  splits~. apply eval_list_rev.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_app : forall H ln1 ln2,
  triple (val_list_app (val_listint ln1) (val_listint ln2)) H
    (fun r => (\[r = val_listint (ln1 ++ ln2)] \* H)).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listint (ln1 ++ ln2)). splits.
  apply eval_list_app. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_blist_rev : forall H lb,
  triple (val_blist_rev (val_listbloc lb))
    H
    ( fun r => \[r = (val_listbloc (rev lb))] \* H ).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listbloc (rev lb)). splits.
  apply eval_blist_rev. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_new_buffer : forall b H,
  triple (val_new_blist b)
    H
    (fun r => \[r= val_listbloc (b::nil)] \* H ).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listbloc (b::nil)). splits.
  apply eval_new_blist. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_blist_buffer : forall b lb H,
  triple (val_blist_buffer b (val_listbloc lb))
    H
    ( fun r => \[r = (val_listbloc (b::lb))] \* H ).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (val_listbloc (b::lb)). splits.
  apply eval_blist_buffer. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_list_hd_bk : forall H ln1,
  triple (val_list_hd_bk (val_listint ln1)) H
    (fun r => (\[r = val_listint (take 2%nat ln1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (take 2%nat ln1)).
  splits~. apply eval_list_hd_blk.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_tl_bk : forall H ln1,
  triple (val_list_tl_bk (val_listint ln1)) H
    (fun r => (\[r = val_listint (drop 2%nat ln1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (drop 2%nat ln1)).
  splits~. apply eval_list_tl_blk.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.


Lemma triple_list_hd : forall H ln1,
  triple (val_list_hd (val_listint ln1)) H
    (fun r => (\[r = val_listint (take 1%nat ln1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (take 1%nat ln1)).
  splits~. apply eval_list_hd.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_tl : forall H ln1,
  triple (val_list_tl (val_listint ln1)) H
    (fun r => (\[r = val_listint (drop 1%nat ln1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (drop 1%nat ln1)).
  splits~. apply eval_list_tl.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

Lemma triple_list_len : forall H ln1,
  triple (val_list_len (val_listint ln1)) H
    (fun r => (\[r = (LibList.length ln1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (LibList.length ln1).
  splits~. apply eval_list_len.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

(* ----------------  SL rule: terms   --------------- *)
Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof.
  introv M. unfold triple. intros. applys hoare_val.
  applys~ himpl_frame_l.
Qed.

Lemma triple_val' : forall v H,
  triple (trm_val v) H (fun r => \[r = v] \* H).
Proof.
  introv M. unfold triple. intros.
  exists sf sb v. splits~. apply eval_val.
  rewrite hstar_assoc, hstar_hpure_iff.
  splits~.
Qed.

Lemma triple_fix: forall F x t1 H Q,
  H ==> Q (val_fix F x t1) ->
  triple (trm_fix F x t1) H Q.
Proof.
  unfold triple. introv M.
  intros Hf' Hb' hf hb K.
  exists hf hb __.
  splits~. apply eval_fix.
  eapply himpl_frame_l in M.
  applys M K.
Qed.

Lemma triple_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv E M1. intros Hf Hb. applys hoare_eval_like E. applys M1.
Qed.

Lemma triple_trm_equiv : forall t1 t2 H Q,
  trm_equiv t1 t2 ->
  triple t1 H Q <-> triple t2 H Q.
Proof using.
  introv E. unfolds trm_equiv. iff M.
  { applys triple_eval_like M. introv R. applys* E. }
  { applys triple_eval_like M. introv R. applys* E. }
Qed.

Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof.
  introv M.
  unfold triple. intros Hf Hb hf hb K.  
  exists hf hb __. splits~. applys eval_fun.
  eapply himpl_frame_l in M.
  applys M K.
Qed.

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof.
  introv M N.
  applys triple_eval_like N.
  introv R. applys eval_app_fun M R.
Qed.

Lemma triple_app_fix : forall v1 v2 F x t1 H Q,
  v1 = val_fix F x t1 ->
  triple (subst x v2 (subst F v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof.
  introv M N.
  applys triple_eval_like N.
  introv R. applys eval_app_fix M R.
Qed.

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof.
  introv M1 M2. intros Hf Hb hf hb M.
  forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  forwards* (hf2&hb2&v2&R2&K2): (rm M2).
  exists hf2 hb2 v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma triple_let :forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof.
  introv M1 M2. intros Hf Hb hf hb M.
  forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  forwards* (hf2&hb2&v2&R2&K2): (rm M2).
  exists hf2 hb2 v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma triple_if : forall be t1 t2 H Q,
  triple (if be then t1 else t2) H Q ->
  triple (trm_if (val_bool be) t1 t2) H Q.
Proof.
  introv M. intros Hf Hb hf hb K.
  forwards* (hf1&hb1&v1&R1&K1): (rm M).
  exists hf1 hb1 v1. splits~. { applys* eval_if. }
Qed.


(* ------------ SL structural rules ----------------- *)

(*  _______________Frame Rule in CBS__________________  *)
Lemma triple_frame : forall t H Q Hf Hb,
  triple t H Q ->
  triple t (H \* (\R[Hf,Hb])) (Q \*+ (\R[Hf,Hb])).
Proof.
  unfold triple, hoare. introv M.
  intros Hf' Hb' sf sb.
  specializes M (Hf \f* Hf') (Hb \b* Hb'). introv N.
  rewrite hstar_assoc, hstar_sep in N.
  apply M in N as (sf'&sb'&v&N1&N2).
  exists sf' sb' v.
  rewrite hstar_assoc, hstar_sep. splits~.
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof.
  introv M N R.
  unfolds triple.
  intros Hf Hb. specializes M Hf Hb.
  applys hoare_conseq.
  applys M. applys~ himpl_frame_l.
  intros v. applys~ himpl_frame_l.
Qed.

(*prove by hoare triple*)
Lemma triple_conseq' : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof.
  unfolds triple, hoare.
  introv M MH MQ HF.
  forwards (sf'&sb'&v&R&K): M sf sb. {applys~ himpl_frame_l MH HF. }
  exists sf' sb' v. splits~. { applys~ himpl_frame_l. }
Qed.

Lemma triple_conseq_frame : forall H Q Hf Hb H1 Q1 t ,
  triple t H1 Q1 ->
  H ==> H1 \* (\R[Hf, Hb]) ->
  Q1 \*+ (\R[Hf, Hb]) ===> Q ->
  triple t H Q.
Proof.
  introv M N R.
  unfolds triple.
  intros Hf' Hb'.
  specializes M (Hf \f* Hf') (Hb \b* Hb').
  applys hoare_conseq. applys M.
  rewrite <- hstar_sep, <- hstar_assoc;
  applys~ himpl_frame_l.
  intros v. rewrite <- hstar_sep. rewrite <- hstar_assoc.
  applys~ himpl_frame_l.
Qed.

(*prove by hoare triple*)
Lemma triple_conseq_frame' : forall H Q Hf Hb H1 Q1 t ,
  triple t H1 Q1 ->
  H ==> H1 \* (\R[Hf, Hb]) ->
  Q1 \*+ (\R[Hf, Hb]) ===> Q ->
  triple t H Q.
Proof.
  introv M N R.
  unfolds triple, hoare.
  intros Hf' Hb' sf sb ((sf1&sb1)&(sf2&sb2)&MA&MB&MC&MD).
  forwards (sf'&sb'&v&T&K): M sf sb. rewrite MD.
  lets K : himpl_frame_l (\R[Hf',Hb']) H (H1 \* (\R[Hf,Hb])).
  rewrite hstar_assoc, hstar_sep in K.
  apply K in N.  applys~ himpl_frame_l N. applys~ hstar_intro.
  exists sf' sb' v. splits~.
  applys~ himpl_frame_l. rewrite hstar_assoc, hstar_sep. auto.
Qed.

Lemma triple_ramified_frame : forall H1 t Hf Hb H Hf1 Hb1,
  triple t H1 (fun r => \R[Hf1,Hb1]) ->
  H ==> H1 \* (\R[Hf1 \f-* Hf, Hb1 \b-* Hb] ) ->
  triple t H (fun r => \R[Hf,Hb]).
Proof.
  introv M W.
  applys triple_conseq_frame M W.
  intros v.
  applys himpl_trans himpl_frame_r.
  apply hwand_refine.
  apply hwand_cancel.
Qed.


(*====== ramified_frame  ======*)
(*Lemma triple_conseq_frame_of_ramified_frame : forall H2 H1 Hf1 Hb1 t H Hf Hb,
  triple t H1 (fun r => \R[Hf1,Hb1]) ->
  H ==> H1 \* H2 ->
  (fun (r:val) => \R[Hf1,Hb1]) \*+ H2 ===> (fun r => \R[Hf,Hb]) ->
  triple t H (fun r => \R[Hf,Hb]).
Proof.
  introv M WH WQ. applys triple_ramified_frame M.
  applys himpl_trans WH.
  applys himpl_frame_r.
  applys himpl_trans.
  rewrite qwand_equiv. applys WQ.
Qed.*)


(*---------- extract the prue fact and quantifier from precondition ----------*)
Lemma triple_hpure : forall t (P:Prop) Hf Hb Q,
  (P -> triple t (\R[Hf,Hb]) Q) ->
  triple t (\[P] \* \R[Hf,Hb]) Q.
Proof.
  unfold triple. intros. rewrite hstar_assoc,hstar_sep.
  intros hf hb M. apply hstar_hpure_iff in M as [MA MB].
  applys~ H. rewrite~ hstar_sep.
Qed.

Lemma triple_hpure' : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof.
  unfold triple. intros. rewrite hstar_assoc.
  intros hf hb M. apply hstar_hpure_iff in M as [MA MB].
  applys~ H0.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (\exists (x:A), J x) Q.
Proof.
  unfold triple. intros.  intros hf hb M.
  rewrite hstar_hexists in M.
  destruct M as (v&M). specializes H v. applys~ H.
Qed.

Lemma triple_hbpure : forall t (P:Prop) Hf Hb Q,
  (P -> triple t (\R[Hf,Hb]) Q) ->
  triple t (\R[Hf,\b[P] \b* Hb]) Q.
Proof.
  unfold triple.
  intros. intros hf hb. rewrite hstar_sep.
  intros (MA&MB). simpls.
  rewrite hbstar_assoc in MB.
  apply hbstar_hpure_iff in MB as [MB1 MB2].
  eapply H in MB1. apply MB1.
  rewrite hstar_sep. splits~.
Qed.

Lemma triple_hfpure : forall t (P:Prop) Hf Hb Q,
  (P -> triple t (\R[Hf,Hb]) Q) ->
  triple t (\R[\f[P] \f* Hf,Hb]) Q.
Proof.
  unfold triple.
  intros. intros hf hb. rewrite hstar_sep.
  intros (MA&MB). simpls.
  rewrite hfstar_assoc in MA.
  apply hfstar_hpure_iff in MA as [MA1 MA2].
  eapply H in MA1. apply MA1.
  rewrite hstar_sep. splits~.
Qed.

Lemma triple_hbpure' : forall t (P:Prop) Hf Q,
  (P -> triple t (\R[Hf,\b[]]) Q) ->
  triple t (\R[Hf,\b[P]]) Q.
Proof.
  intros. lets M : triple_hbpure \b[].
  rewrite~ hbstar_hempty_r in M.
Qed.

Lemma triple_hfpure' : forall t (P:Prop) Hb Q,
  (P -> triple t (\R[\f[],Hb]) Q) ->
  triple t (\R[\f[P],Hb]) Q.
Proof.
  intros. lets M : triple_hfpure \f[].
  rewrite~ hfstar_hempty_r in M.
Qed.

Lemma triple_hbexists : forall t (A:Type) (J:A->hbprop) Hf Hb Q,
  (forall (x:A), triple t (\R[ Hf, (J x) \b* Hb]) Q) ->
  triple t (\R[ Hf, (\existsb (x:A), J x) \b* Hb]) Q.
Proof.
  unfold triple. intros. rewrite hstar_sep, hbstar_assoc.
  intros hf hb (MA&MB). simpls.
  rewrite hbstar_hexists in MB.
  destruct MB as (v&MB).
  specializes H v. apply H.
  rewrite hstar_sep. splits~. rewrite~ hbstar_assoc.
Qed.

Lemma triple_hbexists' : forall t (A:Type) (J:A->hbprop) Hf Q,
  (forall (x:A), triple t (\R[ Hf, (J x)]) Q) ->
  triple t (\R[ Hf, (\existsb (x:A), J x)]) Q.
Proof.
  intros. lets M : triple_hbexists \b[].
  rewrite~ hbstar_hempty_r in M. apply M.
  intros. rewrite~ hbstar_hempty_r.
Qed.

Lemma triple_hfexists : forall t (A:Type) (J:A->hfprop) Hf Hb Q,
  (forall (x:A), triple t (\R[(J x)\f*Hf, Hb]) Q) ->
  triple t (\R[ (\existsf (x:A), J x) \f*Hf, Hb]) Q.
Proof.
  unfold triple. intros. rewrite hstar_sep, hfstar_assoc.
  intros hf hb (MA&MB). simpls.
  rewrite hfstar_hexists in MA.
  destruct MA as (v&MA).
  specializes H v. apply H.
  rewrite hstar_sep. splits~. rewrite~ hfstar_assoc.
Qed.

Lemma triple_hfexists' : forall t (A:Type) (J:A->hfprop) Hb Q,
  (forall (x:A), triple t (\R[ (J x), Hb]) Q) ->
  triple t (\R[ (\existsf (x:A), J x), Hb]) Q.
Proof.
  intros. lets M : triple_hfexists \f[].
  rewrite~ hfstar_hempty_r in M. apply M.
  intros. rewrite~ hfstar_hempty_r.
Qed.

(*==================== AUX inner specification==============================*)
Lemma hoare_bcreate' : forall Hf Hb ln,
  hoare (bprim_create (val_listint ln))
    (\R[ Hf, Hb])
    (fun r => \R[ Hf, \existsb b, \b[r = val_bloc b] \b* b ~b~> ln \b* Hb ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  forwards~ (b&D&N): (Fmap.single_fresh 0%nat sb ln).
  exists sf ((Fmap.single b ln) \u sb) (val_bloc b). subst.
  simpls. splits~.
  (*Notice!!*)
  - applys~ eval_bcreate_sep.
  - splits~. exists b.
    rewrite <- hbstar_assoc.
    applys~ hbstar_intro.
    rewrite~ hbstar_hpure. splits~.
    applys~ hbsingle_intro.
Qed.

Lemma triple_bcreate' : forall Hf ln,
  triple (bprim_create (val_listint ln))
    (\R[ Hf, \b[] ])
    (fun r => (\R[ Hf, (\existsb b, \b[r= (val_bloc b)] \b* b ~b~> ln)]) ).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_bcreate' hstar_sep_l.

  intros r h M.
  destruct M as (MA&MB).
  rewrite hstar_sep, state_get_eq.
  splits~. simpls.
  destruct MB as (pb&MB).
  rewrite hbstar_hexists. exists pb.
  apply hbstar_hpure_iff in MB as [MB1 MB].
  rewrite hbstar_comm, hbstar_assoc, hbstar_hempty_l in MB.
  rewrite~ hbstar_assoc. rewrite hbstar_hpure_iff.
  splits~. rewrite~ hbstar_comm.
Qed.

(*====================== Optimization for Multi arguments =========================*)

(*--- two arguments ---*)
Lemma eval_like_app_fun2 : forall v0 v1 v2 x1 x2 t1,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  (x1 <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 t1)) (v0 v1 v2).
Proof using.
  introv E N. introv R.
  applys~ eval_app_args.
  - applys~ eval_app_fun E. simpl.
    rewrite var_eq_spec. case_if.
    applys eval_fun.
  - applys eval_val.
  - applys* eval_app_fun.
Qed.

Lemma eval_like_app_fix2 : forall F v0 v1 v2 x1 x2 t1,
  v0 = val_fix F x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ F <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 (subst F v0 t1))) (v0 v1 v2).
Proof using.
  introv E (N1&N2). introv R.
  applys~ eval_app_args.
  - applys~ eval_app_fix E. simpl.
    do 2 (rewrite var_eq_spec; case_if).
    applys eval_fun.
  - applys eval_val.
  - applys* eval_app_fun.
Qed.

Lemma triple_app_fun2 : forall x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fun x1 (trm_fun x2 t1) ->
  (x1 <> x2) ->
  triple (subst x2 v2 (subst x1 v1 t1)) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fun2.
Qed.

Lemma triple_app_fix2 : forall F x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix F x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ F <> x2) ->
  triple (subst x2 v2 (subst x1 v1 (subst F v0 t1))) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fix2.
Qed.

(* --- three args --- *)

Lemma eval_like_app_fun3 : forall v0 v1 v2 v3 x1 x2 x3 t1,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2  /\ x1 <> x3 /\ x2 <> x3) ->
  eval_like (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) (v0 v1 v2 v3).
Proof.
  introv E (N1&N2&N3). introv R. applys* eval_app_args.
  { applys* eval_like_app_fun2 E. simpl. do 2 (rewrite var_eq_spec; case_if). applys eval_fun. }
  { applys eval_val. }
  { applys* eval_app_fun. }
Qed.

Lemma triple_app_fun3 : forall x1 x2 x3 v0 v1 v2 v3 t1 H Q,
  v0 = val_fun x1 (trm_fun x2 (trm_fun x3 t1)) ->
  (x1 <> x2  /\ x1 <> x3 /\ x2 <> x3) ->
  triple (subst x3 v3 (subst x2 v2 (subst x1 v1 t1))) H Q ->
  triple (v0 v1 v2 v3) H Q.
Proof.
  introv E (N1&N2&N3) M.
  applys triple_eval_like M. applys* eval_like_app_fun3.
Qed.

(*================== Reasoning rules for mapreduce ===========================*)
(** ++++++++++++++++++++  Hoare Reasoning rules  ++++++++++++++++++++ **)

(*------------ mapper opertions -------------------*)
Lemma hoare_wdmap : forall Hf Hb b ln,
  hoare (bMR_mapper (val_bloc b))
    (\R[ Hf, ( (b ~b~> ln) \b* Hb) ])
    ( fun r => \[r = (WCval_listwdpair (List.map init ln))] \* \R[ Hf, ((b ~b~> ln) \b* Hb)] ).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (WCval_listwdpair (List.map init ln)). subst.
  splits~.
  - lets (E1&N) : hbsingle_inv D1. subst. simpls.
    applys~ eval_wdmap_sep. apply D4.
  - rewrite~ hstar_hpure. splits~. splits~. simpls. substs~.
    applys~ hbstar_intro.
Qed.

(*-------- reducer --------*)

Lemma hoare_wdmerge : forall H Lwd,
  hoare (fMR_merge (WCval_Listwd Lwd)) H
    (fun r => (\[r = WCval_listwdpair (fold_right app nil Lwd)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (WCval_listwdpair (fold_right app nil Lwd)). splits.
  apply eval_merge.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_wdreduce : forall H Lwd,
  hoare (fMR_reducer (WCval_Listwd Lwd)) H
    (fun r => (\[r = WCval_listwdpair (List.map accmulate Lwd)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (WCval_listwdpair (List.map accmulate Lwd)). splits.
  apply eval_wdreduce.
  applys* hstar_hpure_iff.
Qed.
(*------------------ SL rule: mapper ---------------*)

(** WordCount mapper rules **)
Lemma triple_wdmap : forall Hf b ln,
  triple (bMR_mapper (val_bloc b))
    (\R[ Hf, (b ~b~> ln) ])
    ( fun r => \[r = (WCval_listwdpair (List.map init ln))] \* \R[ Hf, (b ~b~> ln)] ).
Proof.
  intros. unfold triple. intros Hf' Hb'.
  applys hoare_conseq hoare_wdmap.
  rewrite hstar_sep. apply himpl_refl.
  intros r h R.
  rewrite hstar_hpure_iff in R.
  destruct R as (RA&RB).
  rewrite hstar_assoc. rewrite hstar_hpure.
  splits~. rewrite~ hstar_sep.
Qed.

(*------------------ SL rule: reducer ---------------*)

(** WordCount reducer rules **)
Lemma triple_wdmerge : forall H Lwd,
  triple (fMR_merge (WCval_Listwd Lwd)) H
    (fun r => (\[r = WCval_listwdpair (fold_right app nil Lwd)] \* H)).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (WCval_listwdpair (fold_right app nil Lwd)). splits.
  apply eval_merge. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_wdgroup : forall H lwd,
  triple (fMR_group (WCval_listwdpair lwd)) H
    (fun r => (\[r = WCval_Listwd (remove_duplicates (classify lwd lwd))] \* H)).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (WCval_Listwd (remove_duplicates (classify lwd lwd))). splits.
  apply eval_group. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_wdreduce : forall H Lwd,
  triple (fMR_reducer (WCval_Listwd Lwd)) H
    (fun r => (\[r = WCval_listwdpair (List.map accmulate Lwd)] \* H)).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (WCval_listwdpair (List.map accmulate Lwd)). splits.
  apply eval_wdreduce. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

(* rules for aux list operations *)
Lemma triple_app_wdlist : forall H l L,
  triple (val_app_wdlist (WCval_listwdpair l) (WCval_Listwd L)) H
    (fun r => (\[r = WCval_Listwd (l :: L)] \* H)).
Proof.
  intros. intros Hf Hb sf sb M.
  exists sf sb (WCval_Listwd (l :: L)). splits.
  apply eval_app_wdlist. rewrite hstar_assoc.
  applys* hstar_hpure_iff.
Qed.

Lemma triple_MRlist_reform : forall H l1,
  triple (val_reform (WCval_listwdpair l1)) H
    (fun r => (\[r = val_listint (kv2int l1)] \* H)).
Proof.
  intros. unfold triple. intros Hf Hb sf sb M.
  exists sf sb (val_listint (kv2int l1)).
  splits~. apply eval_reform.
  rewrite hstar_assoc.
  apply* hstar_hpure_iff.
Qed.

(* ================================================================================ *)
