(**

This file describes the representation and verification of some CBS data modifications.

Examples are mainly about:
  1. Move a block
  2. Append
  3. Truncate

Notice: readers need to read Language.v and ExBasic.v firstly.

Author: Bowen Zhang.

Date : 2022.03.21
*)

From SLF (* TLC *) Require Export LibCore TLCbuffer.
From SLF (* Sep *) Require Export Rules ExBasic.

(* ###########################  Examples #################################*)

(* !! Need to read the Language.v and ExBasic.v firstly !! *)
Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.

(*========================= Move a block ================================*)
Definition Move_blk :=
  Fun 'f 'i :=
    Let 'bk := 'nth_blk 'f 'i in
    Let 'bk1 := Copy_blk 'bk in
    'set_nth_blk 'f 'i 'As 'bk1 ';
    'bdelete 'bk.

Lemma triple_Move_blk : forall (fp:floc) (bp:bloc) (lb:list bloc) (ln:list int) (n:int),
  bp = (nth_default bnull (Z.to_nat n) lb) ->
  triple (Move_blk fp n)
    (\R[ fp ~f~> lb, bp ~b~> ln ])
    (fun _ => \exists bp',
              (\R[( fp ~f~> (LibList.update (to_nat n) bp' lb)),(bp' ~b~> ln)])).
Proof.
  introv ->.
  applys* triple_app_fun2. simpls.
  applys triple_let triple_fget_nth_blk. ext.
  applys triple_let triple_Copy_blk.
  ext. intros bp'. ext.
  applys triple_seq.
  apply triple_fset_nth_blk.
  applys triple_conseq_frame triple_bdelete.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_comm.
  applys himpl_refl.
  intros r. rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l.
  intros h (MA&MB).
  exists bp'. splits~.
Qed.

(*=================== Append =========================*)

Definition Append_blk :=
  Fun 'f 'l :=
    Let 'bk := 'bcreate 'l in
    Let 'lb := 'fbuffer 'bk in
    'fatt 'f 'lb.

(* a smallfoot specification that only describes *)
Lemma triple_Append_blk: forall lb ln (f:floc) ,
  triple (Append_blk f (val_listint ln))
    (\R[f ~f~> lb, \b[]])
    (fun _ => \exists bp, \R[f ~f~> (lb++(bp::nil)), bp ~b~> ln]).
Proof.
  intros. applys* triple_app_fun2. simpl.
  applys triple_let triple_bcreate. ext. intros bp1. ext.
  applys triple_let triple_fbuffer. ext.
  applys triple_conseq_frame triple_fattach.
  rewrite hstar_hempty_r'.
  intros h (MA&MB). splits.
  rewrite hfstar_hpure. splits. apply noduplicates_one.
  apply MA. apply MB.
  intros r. rewrite hstar_hempty_r'.
  intros h M. exists~ bp1.
Qed.

(* ----------------generalize to a specific file---------------- *)
(*
Before append, the file only has one block whose content is (n1,n2).
After the operation, the file has two blocks, and its last block has content as (n3).
*)
Lemma triple_Append_blk_gen: forall (p1:bloc) (n1 n2 n3:int) (f:floc) ,
  triple (Append_blk f (val_listint (n3::nil)))
    (\R[ f ~f~> (p1::nil), p1 ~b~> (n1::n2::nil) ])
    (fun _ => \exists bp, \R[f ~f~> (p1::bp::nil), (p1 ~b~> (n1::n2::nil)) \b* (bp ~b~> (n3::nil))]).
Proof.
  intros.
  applys triple_conseq_frame.
  applys triple_Append_blk.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l.
  applys himpl_refl.
  intros r h H. rewrite hstar_hexists in H.
  destruct H as (bp&H).
  rewrite hstar_sep, hfstar_hempty_r in H.
  rew_list in H.
  exists bp. rewrite~ hbstar_comm.
Qed.


(*-------Some auto proof script for reasoning about truncate-------*)
Fact nat_min_2_1: (2%nat - 1%nat) = 1%nat.
Proof. math. Qed.

Fact le_2_1: (2%nat <= 1%nat) = False.
Proof. auto. Qed.

Fact le_1_2': (1%nat <= 2%nat) = True.
Proof. apply prop_eq_True. discriminate. Qed.

Fact le_0_2: (0%nat <= 2%nat) = True.
Proof. apply prop_eq_True. discriminate. Qed.

Lemma le_1_2: ((2%nat - 1%nat) <= 2%nat) = True.
Proof. apply prop_eq_True. discriminate. Qed.

(* Hint Resolve to_nat_min_add min_2_1 nat_min_2_1 nat_min_1_2 le_2_1 nth_listbloc_2. *)

Ltac inner_femp_r:=
  try rewrite hstar_sep;
  try rewrite hfstar_hempty_r;
  try rewrite hbstar_comm3;
  apply himpl_refl.

Ltac ext':=
  intros r; simpl;
  try rewrite hstar_assoc;
  try rewrite hstar_sep; 
  ext.

Ltac run2time :=
  applys* triple_app_fix2; simpl;
  applys triple_let triple_fsize; ext;
  applys triple_let triple_min; ext;
  applys triple_let triple_fget_nth_blk; ext;
  applys triple_let;
  try applys triple_conseq_frame triple_bsize.

(*===================== Truncate files ===========================*)
(*
  n : truncate range
  m : file size
  m1 : the index of last block
  bk : the last block
  m2 : block size
  n2 : new truncate range after a recursion
  r1,r2 : ignored value
*)
Definition Truncate : val :=
  Fix 'F 'f 'n :=
    Let 'm := 'fsize 'f in
    Let 'm1 := 'm '- 1%nat in
    Let 'bk := 'nth_blk 'f 'm1 in
    Let 'm2 := 'bsize 'bk in
    Let 'be := ('n '<= 'm2) in
    If_ 'be
    Then
      'btrun 'bk 'n
    Else
      Let 'n2 := 'n '- 'm2 in
      Let 'r1 := 'bdelete 'bk in
      Let 'r2 := 'ftrun 'f 1 in
      'F 'f 'n2.

Lemma triple_Truncate: forall Hf Hb (f:floc) (p1 p2 p3:bloc) (n1 n2 n3 n4 n5:int),
  Hf = ( f ~f~> (p1::p2::p3::nil) ) ->
  Hb = ( (p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::n4::nil)) \b* (p3 ~b~> (n5::nil)) ) ->
  triple (Truncate f 2%nat)
    (\R[Hf,Hb])
    (fun _ => \R[f ~f~> (p1::p2::nil),(p1 ~b~> (n1::n2::nil)) \b* (p2 ~b~> (n3::nil))]).
Proof.
  introv M N. subst. applys* triple_app_fix2. simpl.
  applys triple_let triple_fsize. ext.
  applys triple_let triple_min. ext.
  applys triple_let triple_fget_nth_blk. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bsize. inner_femp_r.
  intros r. applys himpl_refl. ext'.
  applys triple_let triple_le. ext.
  applys triple_if. rewrite le_2_1. case_if*.
  applys triple_let triple_min. ext.
  applys triple_let.
  applys triple_conseq_frame triple_bdelete.
  rewrite hstar_sep. applys himpl_refl.
  intros r. rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l. applys himpl_refl.
  intros. simpl. applys triple_let triple_ftruncate.
  intros. simpl. unfold droplast. simpl. rew_list.
  (* the second round *)
  run2time.
  rewrite hstar_sep, hfstar_hempty_r. apply himpl_refl.
  intros r. applys himpl_refl. ext'.
  applys triple_let triple_le. ext.
  applys triple_if. rewrite le_1_2. case_if*.
  applys triple_conseq_frame triple_btruncate.
  rewrite hstar_sep. applys himpl_refl.
  intros r. rewrite hstar_sep, hfstar_hempty_r.
  unfold droplast. simpl. rew_list.
  rewrite hbstar_comm. applys himpl_refl.
Qed.