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
From SLF (* Sep *) Require Export TripleAndRules ExBasic.

(* ###########################  Examples #################################*)

(* !! Need to read the Language.v and ExBasic.v firstly !! *)
Export NotationForTrm.
Export NotationForVariables.

Open Scope val_scope.
Open Scope trm_scope.
Open Scope Z_scope.


(* Lemma nodup_after_shuffle : forall lwd,
  noduplicates (wordshuffle lwd).
Proof.
  intros. unfolds wordshuffle.
  induction lwd.
  unfold shuffle. simpl. apply noduplicates_nil.
  unfold shuffle in IHlwd. unfold shuffle. simpl.
  case_if*.
  2: { simpl. destruct C. unfold eqword. auto. }
  unfold remove,remove_duplicates,classify.
  simpl. *)

(*=================== Append a block =========================*)

Definition Append_a_blk :=
  Fun 'f 'l :=
    Let 'bk := 'bcreate 'l in
    Let 'lb := 'buffer 'bk in
    'fatt 'f 'lb.

(* a smallfoot specification that only describes *)
Lemma triple_Append_a_blk: forall lb ln (f:floc) ,
  triple (Append_a_blk f (val_listint ln))
    (\R[f ~f~> lb, \b[]])
    (fun _ => \exists bp, \R[f ~f~> (lb++(bp::nil)), bp ~b~> ln]).
Proof.
  intros. applys* triple_app_fun2. simpl.
  applys triple_let triple_bcreate. ext. intros bp1. ext.
  applys triple_let triple_new_buffer. ext.
  applys triple_conseq_frame triple_fattach.
  rewrite hstar_hempty_r'.
  intros h (MA&MB). splits.
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
  triple (Append_a_blk f (val_listint (n3::nil)))
    (\R[ f ~f~> (p1::nil), p1 ~b~> (n1::n2::nil) ])
    (fun _ => \exists bp, \R[f ~f~> (p1::bp::nil), (p1 ~b~> (n1::n2::nil)) \b* (bp ~b~> (n3::nil))]).
Proof.
  intros.
  applys triple_conseq_frame.
  applys triple_Append_a_blk.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l.
  applys himpl_refl.
  intros r h H. rewrite hstar_hexists in H.
  destruct H as (bp&H).
  rewrite hstar_sep, hfstar_hempty_r in H.
  rew_list in H.
  exists bp. rewrite~ hbstar_comm.
Qed.

(*=================== Append contents =========================*)
Definition AppendBlks : val :=
  Fix 'F 'f 'l :=
    Let 'm := 'len 'l in
    Let 'be := ('m '<= 2) in
    If_ 'be
    Then 
      Append_a_blk 'f 'l
    Else
      Let 'l1 := 'hdblk 'l in
      Let 'l2 := 'tlblk 'l in
      Let 'r := Append_a_blk 'f 'l1 in
        'F 'f 'l2.

Lemma triple_AppendBlks: forall (b1:bloc) (n1 n2 n3 n4 n5:int) (f:floc) ,
  triple (AppendBlks f (val_listint (n3::n4::n5::nil)))
    (\R[ f ~f~> (b1::nil), b1 ~b~> (n1::n2::nil) ])
    (fun _ => \exists b2 b3, 
      \R[f ~f~> (b1::b2::b3::nil), 
         (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil)) \b* (b3 ~b~> (n5::nil))]).
Proof.
  intros. applys* triple_app_fix2. simpl.
  applys triple_let triple_list_len.
  ext. applys triple_let triple_le. ext.
  applys triple_if. case_if*. destruct C. auto.
  applys triple_let triple_list_hd_bk. ext.
  applys triple_let triple_list_tl_bk. ext.
  applys triple_let.
  applys triple_conseq_frame triple_Append_a_blk.
  rewrite hstar_sep. rewrite hfstar_hempty_r, hbstar_hempty_l.
  apply himpl_refl. intros r. simpl.
  apply himpl_refl.
  
  intros r.
  rewrite hstar_hexists.
  applys triple_hexists. intros p2.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_comm.
  applys* triple_app_fix2. simpl.
  applys triple_let triple_list_len. ext.
  applys triple_let triple_le. ext.
  applys triple_if. case_if*.
  2: { destruct C0. rew_list. discriminate. }
  applys triple_conseq_frame triple_Append_a_blk.
  rewrite hstar_sep, hfstar_hempty_r, hbstar_hempty_l. apply himpl_refl.
  rewrite hstar_hexists. apply himpl_hexists_append.
Qed.


Definition AppendFile : val :=
  Fun 'f 'l :=
    Let 'm := 'fsize 'f in
    Let 'm1 := 'm '- 1%nat in
    Let 'b := 'nthblk 'f 'm1 in
    Let 'm2 := 'bsize 'b in
    Let 'be := ('m '<= 2%nat) in
    If_ 'be
    Then 
      Let 'k := 'hd 'l in
      Let 'l2 := 'tl 'l in
      Let 'r := 'bapp 'b 'k in 
        AppendBlks 'f 'l2
    Else
      AppendBlks 'f 'l.

Fact le_1_2': (1%nat <= 2%nat) = True.
Proof. apply prop_eq_True. discriminate. Qed.

Lemma triple_AppendFile: forall (b1:bloc) (n1 n2 n3 n4 n5:int) (f:floc) ,
  triple (AppendFile f (val_listint (n2::n3::n4::n5::nil)))
    (\R[ f ~f~> (b1::nil), b1 ~b~> (n1::nil) ])
    (fun _ => \exists b2 b3, 
      \R[f ~f~> (b1::b2::b3::nil), 
         (b1 ~b~> (n1::n2::nil)) \b* (b2 ~b~> (n3::n4::nil)) \b* (b3 ~b~> (n5::nil))]).

Proof.
  intros. applys* triple_app_fun2. simpls.
  applys triple_let triple_fsize. ext.
  applys triple_let triple_min. ext.
  applys triple_let triple_fget_nth_blk. ext.
  applys triple_let triple_bsize. ext.
  applys triple_let triple_le. ext.
  applys triple_if. rewrite le_1_2'. case_if*.
  applys triple_let triple_list_hd. ext.
  applys triple_let triple_list_tl. ext.
  applys triple_let triple_bappend. ext. rew_list.
  applys triple_conseq_frame triple_AppendBlks.
  rewrite hstar_hempty_r', nth_default_zero. apply himpl_refl.
  intros r. ext_blk. intros b2. ext_blk. intros b3.
  rewrite hstar_hempty_r'. intros h M.
  exists~ b2 b3.
Qed.


(*-------Some auto proof script for reasoning about truncate-------*)
Fact nat_min_2_1: (2%nat - 1%nat) = 1%nat.
Proof. math. Qed.

Fact le_2_1: (2%nat <= 1%nat) = False.
Proof. auto. Qed.

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
    Let 'bk := 'nthblk 'f 'm1 in
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
  intros. simpl. applys triple_let triple_ftrun.
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