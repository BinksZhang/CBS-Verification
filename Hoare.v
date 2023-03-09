(**

This file mainly describes the Hoare triple and the related rules.
It helps us to construct our formal system.

  1. the definitions of Hoare triple in CBS
  2. the statement and prove of the reasoning rules for Hoare triples.

Author: Bowen Zhang.

Date : 2023.02.21
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* CBS *) Require Export Himpl.

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

(* ================================================================= *)
(** ** Hoare reasoning rules ** **)

(**============= * Definition of (total correctness) Hoare triples ================*)

(* -- the behavior of trm in the entire state -- *)
Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
forall sf sb, H (sf,sb) -> 
  exists sf' sb' v, eval (sf,sb) t (sf',sb') v /\ Q v (sf',sb').

(** ++++++++++++++++++++  Hoare Reasoning rules  ++++++++++++++++++++ **)

(** ----- block prim operations ------- **)
Lemma hoare_bcreate : forall Hf Hb ln,
  hoare (bprim_create (val_listint ln))
    (\R[ Hf, Hb])
    (fun r => \exists b, \[r = val_bloc b] \* \R[ Hf, b ~b~> ln \b* Hb ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  forwards~ (b&D&N): (Fmap.single_fresh 0%nat sb ln).
  exists sf ((Fmap.single b ln) \u sb) (val_bloc b). subst.
  simpls. splits~.
  (*Notice!!*)
  - applys~ eval_bcreate_sep.
  - exists b. rewrite~ hstar_hpure.
    splits~. splits~.
    applys~ hbstar_intro.
    applys~ hbsingle_intro.
Qed.

Lemma hoare_bget : forall Hf Hb b ln,
  hoare (bprim_get (val_bloc b))
    (\R[ Hf, ( (b ~b~> ln) \b* Hb) ])
    ( fun r => \[r = (val_listint ln)] \* \R[ Hf, ((b ~b~> ln) \b* Hb)] ).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (val_listint ln). subst.
  splits~.
  - lets (E1&N) : hbsingle_inv D1. subst. simpls.
    applys~ eval_bget_sep. apply D4.
  - rewrite~ hstar_hpure. splits~. splits~. simpls. substs~.
    applys~ hbstar_intro.
Qed.

Lemma hoare_bdelete : forall Hf Hb b ln,
  hoare (bprim_delete (val_bloc b))
    (\R[ Hf, ( (b ~b~> ln) \b* Hb) ])
    (fun r => \[r = val_unit] \* \R[ Hf, Hb ]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P2 as (sb1&sb2&D1&D2&D3&D4).
  lets (E1&N): hbsingle_inv D1.
  exists sf sb2 (val_unit). subst.
  splits~.
  - simpls. applys~ eval_bdelete_sep. apply D4.
    apply D3.
  - rewrite~ hstar_hpure. splits~. splits~.
Qed.

Lemma hoare_bappend : forall Hf Hb b ln1 ln2,
  hoare (bprim_append (val_bloc b) (val_listint ln2))
    ( \R[Hf, (b ~b~> ln1) \b* Hb] )
    (fun _ => \R[Hf, (b ~b~> (ln1++ln2)) \b* Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K2 as (sb1&sb2&D1&D2&D3&D4).
  lets (E1&N): hbsingle_inv D1.
  subst.
  exists sf (single b (ln1++ln2) \u sb2) val_unit.
  splits.
  - applys~ eval_bappend_sep.
  - splits~. simpl.
    applys~ hbstar_intro.
      + applys~ hbsingle_intro.
      + applys Fmap.disjoint_single_set D3.
Qed.

Lemma hoare_btruncate : forall Hf Hb b ln1 n,
  hoare (bprim_trun (val_bloc b) n)
    ( \R[Hf, (b ~b~> ln1) \b* Hb] )
    (fun _ => \R[Hf, (b ~b~> (droplast (to_nat n) ln1)) \b* Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K2 as (sb1&sb2&D1&D2&D3&D4).
  lets (E1&N): hbsingle_inv D1.
  subst.
  exists sf (single b (droplast (to_nat n) ln1) \u sb2) val_unit.
  splits.
  - applys~ eval_btruncate_sep.
  - splits~. simpl.
    applys~ hbstar_intro.
      + applys~ hbsingle_intro.
      + applys Fmap.disjoint_single_set D3.
Qed.

Lemma hoare_bsize : forall Hf Hb b ln1,
  hoare (bprim_size (val_bloc b) )
    ( \R[Hf, (b ~b~> ln1) \b* Hb] )
    (fun r => \[r = List.length ln1] \* \R[Hf, (b ~b~> ln1) \b* Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K2 as (sb1&sb2&D1&D2&D3&D4).
  exists sf sb (val_int (List.length ln1)).
  lets (E1&N): hbsingle_inv D1. subst.
  splits~.
  applys~ eval_bsize_sep.
  rewrite hstar_hpure_iff.
  splits~. simpl.
  splits~.
  applys~ hbstar_intro.
Qed.

Lemma single_fresh_floc : forall hf lb,
  exists f, Fmap.disjoint (single f lb) hf /\ f <> fnull.
Proof using.
  intros. forwards (f&F&N): exists_not_indom fnull hf.
  exists f. split~. applys* disjoint_single_of_not_indom.
Qed.

(** ------------ file prim operations -------------- **)
Lemma hoare_fcreate : forall Hf Hb lb,
  hoare (fprim_create (val_listbloc lb))
    (\R[ \f[] \f* Hf, Hb ])
    (fun r => \exists f, (\[r = (val_floc f)] \* \R[ (f ~f~> lb) \f* Hf, Hb])).
Proof.
  intros. intros sf sb K0.
  rewrite hfstar_hempty_l in K0.
  destruct K0 as (KA&KB). simpls.
  lets (f&D&N) : single_fresh_floc sf lb.
  exists (Fmap.single f lb \u sf) sb (val_floc f). subst.
  splits~.
  - applys~ eval_fcreate_sep.
  - exists f. rewrite~ hstar_hpure. splits~. splits~. simpls.
    subst. applys~ hfstar_intro. applys~ hfsingle_intro.
Qed.

Lemma hoare_fget : forall Hf Hb f lb,
  hoare (fprim_get (val_floc f))
    (\R[ (f ~f~> lb \f* Hf), Hb])
    (fun r => (\[r = val_listbloc lb]) \* \R[ ((f ~f~> lb) \f* Hf), Hb ]).
Proof.
  intros. intros sf sb ((sf1&sf2&D1&D2&D3&D4)&P2).
  exists sf sb (val_listbloc lb). subst. simpls.
  splits~.
  - lets (E1&N) : hfsingle_inv D1. subst.
    applys~ eval_fget_sep.
  - rewrite hstar_hpure. splits~. splits~. simpls.
    subst. applys~ hfstar_intro.
Qed.

Lemma hoare_fget_nth_blk : forall Hf Hb f lb n,
  hoare (fprim_nthblk (val_floc f) n)
    (\R[ (f ~f~> lb \f* Hf), Hb ])
    (fun r => \[r = val_bloc (nth_default bnull (Z.to_nat n) lb)] \* \R[((f ~f~> lb) \f* Hf),Hb ]).
Proof.
  intros. intros sf sb K.
  destruct K as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  exists sf sb (val_bloc (nth_default bnull (Z.to_nat n) lb)). subst. simpls.
  splits~.
  - lets (E1&N) : hfsingle_inv D1. subst.
    applys~ eval_fget_nth_blk_sep.
  - rewrite hstar_hpure. splits~. splits~. subst. simpls.
    applys~ hfstar_intro.
Qed.

Lemma hoare_fset_nth_blk : forall Hf Hb f lb n b,
  hoare (fprim_set (val_floc f) n (val_bloc b))
    (\R[ (f ~f~> lb \f* Hf), Hb ])
    (fun r => \R[ ( (f ~f~> (LibList.update (to_nat n) b lb)) \f* Hf), Hb ]).
Proof.
  intros. intros sf sb K.
  destruct K as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  exists (single f (LibList.update (to_nat n) b lb) \u sf2) sb val_unit.
  subst. simpls. lets (E1&N) : hfsingle_inv D1.
  splits~.
  - subst~.
    applys~ eval_fset_nth_blk_sep.
  - splits~.
    applys~ hfstar_intro.
      + applys~ hfsingle_intro.
      + applys Fmap.disjoint_single_set.
        rewrite~ <- E1.
Qed.

Lemma hoare_fdelete : forall Hf Hb f lb,
  hoare (fprim_delete (val_floc f))
    (\R[ (f ~f~> lb \f* Hf), Hb ])
    (fun r => \[r = val_unit] \* \R[Hf, Hb]).
Proof.
  intros. intros sf sb K0.
  destruct K0 as (P1&P2).
  destruct P1 as (sf1&sf2&D1&D2&D3&D4).
  lets (E1&N): hfsingle_inv D1.
  exists sf2 sb val_unit. subst. simpls.
  splits~.
  - applys~ eval_fdelete_sep. apply D4. apply D3.
  - rewrite hstar_hpure. splits~. splits~.
Qed.

Lemma hoare_fattach : forall Hf Hb f lb1 lb2,
  hoare (fprim_attach (val_floc f) (val_listbloc lb2))
    ( \R[(\f[] \f* (f ~f~> lb1) \f* Hf), Hb] )
    (fun _ => \R[(f ~f~> (lb1++lb2)) \f* Hf, Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  rewrite hfstar_hempty_l in K1.
  destruct K1 as (sf1&sf2&D1&D2&D3&D4).
  lets (E1&N): hfsingle_inv D1.
  subst.
  exists (single f (lb1++lb2) \u sf2) sb val_unit.
  splits.
  - applys~ eval_fattach_sep.
  - splits~. simpl.
    applys~ hfstar_intro.
      + applys~ hfsingle_intro.
      + applys Fmap.disjoint_single_set D3.
Qed.

Lemma hoare_ftruncate : forall Hf Hb f lb n,
  hoare (fprim_trun (val_floc f) n)
    ( \R[(f ~f~> lb) \f* Hf, Hb] )
    (fun _ => \R[(f ~f~> (droplast (to_nat n) lb)) \f* Hf, Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K1 as (sf1&sf2&D1&D2&D3&D4).
  lets (E1&N): hfsingle_inv D1.
  subst.
  exists (single f (droplast (to_nat n) lb) \u sf2) sb val_unit.
  splits.
  - applys~ eval_ftruncate_sep.
  - splits~. simpl.
    applys~ hfstar_intro.
      + applys~ hfsingle_intro.
      + applys Fmap.disjoint_single_set D3.
Qed.

Lemma hoare_fsize : forall Hf Hb f lb,
  hoare (fprim_size (val_floc f) )
    ( \R[(f ~f~> lb) \f* Hf, Hb] )
    (fun r => \[r = List.length lb] \* \R[(f ~f~> lb) \f* Hf, Hb]).
Proof.
  intros. intros sf sb K.
  destruct K as (K1&K2). simpls.
  destruct K1 as (sf1&sf2&D1&D2&D3&D4).
  exists sf sb (val_int (List.length lb)).
  lets (E1&N): hfsingle_inv D1. subst.
  splits~. applys~ eval_fsize_sep.
  rewrite hstar_hpure_iff.
  splits~. splits~.
  applys~ hfstar_intro.
Qed.

(** -------- aux prim operation  ----------- **)
Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2) H
    (fun r => (\[r = (n1+n2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (n1+n2). splits.
  apply eval_add.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_min : forall H n1 n2,
  hoare (val_min n1 n2) H
    (fun r => (\[r = (n1-n2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (n1-n2). splits.
  apply eval_min.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_le : forall H n1 n2,
  hoare (val_le n1 n2) H
    (fun r => (\[r = (val_bool (isTrue (n1 <= n2)))] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_bool (isTrue (n1 <= n2))). splits.
  apply eval_le.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_eq : forall H n1 n2,
  hoare (val_eq n1 n2) H
    (fun r => (\[r = val_bool (n1 =? n2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_bool (n1 =? n2)). splits.
  apply eval_eq.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_list_rev : forall H ln1,
  hoare (val_list_rev (val_listint ln1)) H
    (fun r => (\[r = val_listint (rev ln1)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_listint (rev ln1)). splits.
  apply eval_list_rev.
  applys* hstar_hpure_iff.
Qed.

Lemma hoare_list_app : forall H ln1 ln2,
  hoare (val_list_app (val_listint ln1) (val_listint ln2)) H
    (fun r => (\[r = val_listint (ln1 ++ ln2)] \* H)).
Proof.
  intros. intros sf sb.
  intros M.
  exists sf sb (val_listint (ln1 ++ ln2)). splits.
  apply eval_list_app.
  applys* hstar_hpure_iff.
Qed.


(** --------- terms  ---------**)
Lemma hoare_eval_like : forall t1 t2 H Q,
  eval_like t1 t2 ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof.
  introv E M1 K0. forwards (sf'&sb'&v&R1&K1) : M1 K0.
  exists sf' sb' v. splits~.
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof.
  introv M. intros hf hb k.
  exists hf hb v. splits~.
  applys eval_val.
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof.
  introv M. intros hf hb k. exists hf hb __.
  splits~. applys eval_fun.
Qed.

Lemma hoare_fix : forall F x t1 H Q,
  H ==> Q (val_fix F x t1) ->
  hoare (trm_fix F x t1) H Q.
Proof.
  introv M. intros hf hb k. exists hf hb __.
  splits~. apply eval_fix.
Qed.

Lemma hoare_app_fun: forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros sf sb K0.
  forwards (sf'&sb'&v&R1&K1) : (rm M) K0.
  exists sf' sb' v.
  splits~. applys eval_app_fun E R1.
Qed.

Lemma hoare_app_fix:forall v1 v2 F x t1 H Q,
  v1 = val_fix F x t1 ->
  hoare (subst x v2 (subst F v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E M. intros sf sb K0. forwards (sf'&sb'&v&R1&K1): (rm M) K0.
  exists sf' sb' v. splits. { applys eval_app_fix E R1. } { applys K1. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  forwards* (hf2&hb2&v2&R2&K2): (rm M2).
  exists hf2 hb2 v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst x v t2) (Q1 v) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  forwards* (hf2&hb2&v2&R2&K2): (rm M2).
  exists hf2 hb2 v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if : forall (be:bool) t1 t2 H Q,
  hoare (if be then t1 else t2) H Q ->
  hoare (trm_if be t1 t2) H Q.
Proof using.
  introv M1. intros hf hb Hh. forwards* (hf1&hb1&v1&R1&K1): (rm M1).
  exists hf1 hb1 v1. splits~. { applys* eval_if. }
Qed.

(*----- structural rules ------*)
Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (sf'&sb'&v&R&K): M sf sb. { applys~ himpl_inv. }
  exists sf' sb' v. splits~. { applys~ himpl_inv. }
Qed.


(* ================================================================================ *)