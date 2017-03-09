Add LoadPath "/home/amos/applpi".

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Import ListNotations.

Record FileSystemState : Set := file_sys_st
  {fs_st : list (string * list bool)}.

(* Helper func: search offset and return content for FS_Read *)
Fixpoint return_offset (content : list bool) (offset : nat) : option bool :=
  match offset with
    | O => match content with (* offset == 0 *)
             | [] => None
             | a :: t => Some a
           end
    | S rest => match content with (* offset != 0 and keeping searching *)
                  | [] => None
                  | a :: t => return_offset t rest
                 end 
  end.

(* Helper func: search file_name in fs and return content of the offset *)
Fixpoint FS_Read (file_name : string) (offset : nat) (file_st : list (string * list bool)) : option bool :=
  match file_st with
    | nil => None
    | a::t => match a with (* compare the file_name and keeping searching from fs *)
             | (s,b) => if string_dec file_name s then return_offset b offset
                        else FS_Read file_name offset t
           end
  end.

(** FS_Read_Main using FS_Read and return_offset *)
Definition FS_Read_Main (file_name : string) (offset : nat) (file_st : FileSystemState) : option bool :=
  match file_st with
    | file_sys_st a => FS_Read file_name offset a
  end.

(* Helper func: search offset and write new content *)
Fixpoint write_content (content : list bool) (offset : nat) (new_content : bool) : option (list bool) :=
  match offset with
    | O => match content with
             | [] => Some [new_content]
             | a :: t => Some (new_content :: t) (* write the new content and the rest appends *)
           end
    | S rest => match content with
                  | [] => None (* if the file doesn't have enough sapce, do nothing *)
                  | a :: t => write_content t rest new_content
                 end 
  end.

(* Helper func: search file_name and offset; then, write the content *)
Fixpoint FS_Write (file_name : string) (offset : nat) (content : bool) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => None
    | a::t => match a with
             | (s,b) => if string_dec file_name s then match write_content b offset content with
                                                         | None => None
                                                         | Some a => Some ((s,a)::t)
                                                        end
                        else match FS_Write file_name offset content t with
                               | None => None
                               | Some b => Some (a::b)
                             end
              end
  end.

(** FS_Write_Main using FS_Write and write_content *)
Definition FS_Write_Main (file_name : string) (offset : nat) (content : bool) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st a => match FS_Write file_name offset content a with
                         | None => None
                         | Some new => Some (file_sys_st new)
                       end
  end.


Fixpoint FS_Create (file_name : string) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => Some [(file_name,nil)]
    | hd::tl => match hd with
                  | (name,content) => if string_dec file_name name then None
                                      else match FS_Create file_name tl with
                                             | None => None
                                             | Some a => Some (hd::a) 
                                           end
                end 
  end.

Definition FS_Create_Main (file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Create file_name st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.

Fixpoint FS_Delete (file_name : string) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => None
    | hd::tl => match hd with
                  | (name, content) => if string_dec file_name name then Some tl
                                       else match FS_Delete file_name tl with
                                              | None => None
                                              | Some a => Some (hd::a)
                                            end
                end
  end.

Definition FS_Delete_Main (file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Delete file_name st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.

Fixpoint FS_Rename (old_file_name : string) (new_file_name : string) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | nil => None
    | hd::tl => match hd with
                  | (name, content) => if string_dec new_file_name name then None
                                       else if string_dec old_file_name name then match FS_Rename old_file_name new_file_name tl with
                                                                                    | None => None
                                                                                    | Some a => Some ((new_file_name, content)::a)
                                                                                   end
                                       else match FS_Rename old_file_name new_file_name tl with
                                              | None => None
                                              | Some a => Some (hd::a)
                                            end
                end                     
  end.

Definition FS_Rename_Main (old_file_name : string) (new_file_name : string) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Rename old_file_name new_file_name st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.

Fixpoint Truncate_Length (new_len : nat) (content : list bool) : option (list bool) :=
  match new_len with 
    | O => Some []
    | S rest => match content with
                  | [] => None
                  | hd::tl => match Truncate_Length rest tl with
                                | None => None
                                | Some new_content => Some (hd::new_content)
                              end
                end
  end.

Fixpoint FS_Truncate (file_name : string) (new_len : nat) (file_st : list (string * list bool)) : option (list (string * list bool)) :=
  match file_st with
    | [] => None
    | hd::tl => match hd with
                  | (name, content) => if string_dec file_name name then match Truncate_Length new_len content with
                                                                           | None => None
                                                                           | Some new_content => Some ((name, new_content)::tl)
                                                                         end
                                       else match FS_Truncate file_name new_len tl with
                                              | None => None
                                              | Some a => Some (hd::a)
                                             end
                 end
  end.

Definition FS_Truncate_Main (file_name : string) (new_len : nat) (file_st : FileSystemState) : option FileSystemState :=
  match file_st with
    | file_sys_st st => match FS_Truncate file_name new_len st with
                          | None => None
                          | Some new => Some (file_sys_st new)
                        end
  end.


Fixpoint Return_List_String (file_st : list (string * list bool)) : list string :=
  match file_st with
    | [] => []
    | hd::tl => match hd with
                  | (name, content) => (name::Return_List_String tl)
                end
  end.

(* retrieve all filenames from the file system *)
Definition Return_All_Filename (file_st : FileSystemState) : list string :=
  match file_st with
    | file_sys_st st => Return_List_String st
  end.

(* Proof: write operation doesn't change the existing file name in the file system *)
Lemma Check_Write_Doesnot_Change_Filename : forall file_st file_name offset content, match FS_Write_Main file_name offset content file_st with 
                                                    | None => True (* write fail means always true *)
                                                    | Some new_st => Return_All_Filename new_st = Return_All_Filename file_st 
                                                    end. (* new and old file names in file system remain the same *)
intros.                                    (* introduce inductive definition *)
destruct file_st.                          (* destruct inductive data type for file_st become fs_st0 *)
simpl.                                     (* compute *)
induction fs_st0.                          (* instantiate fs_st0 into two cases *)
simpl.                                     (* case [] is trivial *)
auto.                                      (* solve the current goal *)
simpl.                                     (* bring FS_Write func in *)
destruct a.                                (* pair is also an inductive type *)
destruct (string_dec file_name s).         (* instantiate if into two cases *)
destruct (write_content l offset content). (* instantiate write_content into its cases *)
simpl.                                     (* compute *)
reflexivity.                               (* equal to *)
auto.                                      (* solve the current goal *)
destruct (FS_Write file_name offset content fs_st0). (* instantiate FS_Write into its cases *)
simpl.                                     (* compute *)
simpl in IHfs_st0.                         (* in induction, we need to use hypothesis *)
rewrite IHfs_st0.                          (* apply IHfs_st0 into current goal *)
reflexivity.                               (* equal to *)
auto.                                      (* solve the current goal *)
Qed.

(* check new string append to the current list of string *)
Fixpoint New_String_Append (list_string : list string) (new_string : string) : list string :=
  match list_string with
    | [] => [new_string]
    | hd::tl => hd::New_String_Append tl new_string
  end.

(* Compare new string to the strings of the list strings in the way of bubble sort *)
Fixpoint Check_StringUnique_List (new_string : string) (list_string : list string) : Prop :=
  match list_string with
    | [] => True
    | hd::tl => ~(new_string = hd) /\ Check_StringUnique_List new_string tl
  end.

(* check all strings are unique in the list strings *)
Fixpoint Check_AllStringUnique_List (list_string : list string) : Prop :=
  match list_string with
    | [] => True
    | hd::tl => Check_StringUnique_List hd tl /\ Check_AllStringUnique_List tl
  end.

(* check all filenames are unique when input is FileSystemState *)
Definition Check_Filename_Unique (file_st : FileSystemState) : Prop :=
  Check_AllStringUnique_List (Return_All_Filename file_st).

(* Proof: write operation doesn't violate the property that all filenames are unique *)
Lemma Check_Write : forall file_st file_name offset content, Check_Filename_Unique file_st -> match FS_Write_Main file_name offset content file_st with 
                                                               | None => True (* write fail means always true *)
                                                               | Some a => Check_Filename_Unique a
                                                             end. (* all filenames are unique after write operation *)
intros.                                                       (* introduce inductive definition *)
destruct file_st.                                             (* destruct inductive data type for file_st become fs_st0 *)
simpl.                                                        (* go into FS_Write_Main *)
pose Check_Write_Doesnot_Change_Filename.                     (* apply other lemma in this proof *)
specialize (y (file_sys_st fs_st0) file_name offset content). (* bring concrete terms for universal quantification of lemma; name new one as y *)
simpl in y.                                                   (* compute for y*)
destruct (FS_Write file_name offset content fs_st0).          (* instantiate FS_write into its cases *)
simpl in y.                                                   (* compute for y *)
unfold Check_Filename_Unique.                                 (* bring function in *)
unfold Return_All_Filename.                                   (* can be replaced by simpl *)
unfold Check_Filename_Unique in H.                            (* bring function in H *)
unfold Return_All_Filename in H.                              (* can be replace by simpl in H *)
rewrite y.                                                    (* apply y into our goal *)
auto.                                                         (* compute *)
auto.                                                         (* solve the current goal *)
Qed.

(* Proof: truncate operation doesn't change the existing file name in the file system *)
Lemma Truncate_Doesnot_Change_Filename : forall file_st file_name length, match FS_Truncate_Main file_name length file_st with 
                                                    | None => True (* truncate fail means always true *)
                                                    | Some new_st => Return_All_Filename new_st = Return_All_Filename file_st 
                                                    end. (* new and old file names in file system remain the same *)
intros.
destruct file_st.
simpl.
induction fs_st0.
simpl.
auto.
simpl.
destruct a.
destruct (string_dec file_name s).
destruct (Truncate_Length length l).
simpl.
reflexivity.
auto.
destruct (FS_Truncate file_name length fs_st0).
simpl.
simpl in IHfs_st0.
rewrite IHfs_st0.
reflexivity.
auto.
Qed.

(* Proof: truncate operation doesn't violate the property that all filenames are unique *)
Lemma Check_Truncate : forall file_st file_name length, Check_Filename_Unique file_st -> match FS_Truncate_Main file_name length file_st with 
                                                               | None => True (* truncate fail means always true *)
                                                               | Some a => Check_Filename_Unique a
                                                             end. (* all filenames are unique after write operation *)
intros.
destruct file_st.
simpl.
pose Truncate_Doesnot_Change_Filename.
specialize (y (file_sys_st fs_st0) file_name length).
simpl in y.
destruct (FS_Truncate file_name length fs_st0).
simpl in y.
unfold Check_Filename_Unique.
unfold Return_All_Filename.
unfold Check_Filename_Unique in H.
unfold Return_All_Filename in H.
rewrite y.
auto.
auto.
Qed.

(* Proof: create operation always append new filename in the end *)
Lemma Check_Create_Append: forall file_st file_name, match FS_Create_Main file_name file_st with
                                    | None => True (* create fail means always true *)
                                    | Some new_st => New_String_Append (Return_All_Filename file_st) file_name = Return_All_Filename new_st
                                  end. (* new and old file names in file system remain the same *)
intros.                                (* introduce inductive definition *)
destruct file_st.                      (* destruct inductive data type for file_st become fs_st0 *)
simpl.                                 (* compute *)
induction fs_st0.                      (* instantiate fs_st0 into two cases *)
simpl.                                 (* case [] is trivial *)
reflexivity.                           (* equal to *)
simpl.                                 (* go into FS_Create *)
destruct a.                            (* pair is also an inductive type *)
destruct (string_dec file_name s).     (* instantiate if into two cases *)
auto.                                  (* solve the current goal *)
destruct (FS_Create file_name fs_st0). (* instantiate FS_Create into its cases *)
simpl.                                 (* compute *)
simpl in IHfs_st0.                     (* in induction, we need to use hypothesis *)
rewrite IHfs_st0.                      (* apply IHfs_st0 into current goal *)
reflexivity.                           (* equal to *)
auto.                                  (* solve the current goal *)
Qed.

(* Proof: create operation always create unique filename in the existing file system *)
Lemma Create_UniqueOne_inFileSys : forall file_st file_name, match FS_Create_Main file_name file_st with 
                                                             | None => True (* truncate fail means always true *)
                                                             | Some a => Check_StringUnique_List file_name (Return_All_Filename file_st)
                                                           end. (* all filenames are unique after create operation *)
intros.
destruct file_st.
simpl.
induction fs_st0.
simpl.
auto.
simpl.
destruct a.
destruct (string_dec file_name s).
auto.
destruct (FS_Create file_name fs_st0).
simpl.
split.
auto.
apply IHfs_st0.
auto.
Qed.

(* Proof: created file is always append and unique *)
Lemma Create_File_AppendUnique : forall file_st file_name, match FS_Create_Main file_name file_st with
                                    | None => True (* truncate fail means always true *)
                                    | Some new_st => Check_StringUnique_List file_name (Return_All_Filename file_st) /\ New_String_Append (Return_All_Filename file_st) file_name = Return_All_Filename new_st
                                  end. (* all filenames are unique after create operation *)
intros.
pose Check_Create_Append.
specialize (y file_st file_name).
pose Create_UniqueOne_inFileSys.
specialize (y0 file_st file_name).
destruct (FS_Create_Main file_name file_st).
tauto.
auto.
Qed.

(* Proof: New_String_Append func doesn't violate the property that all strings are unique *)
(* 1. The new string is diffent from any string in the esisting string list *)
(* 2. The strings in the existing string list are unique *)
Lemma Check_CreatedString : forall old_string_list file_name, Check_StringUnique_List file_name old_string_list ->
                                                       Check_AllStringUnique_List old_string_list -> 
                                                       Check_AllStringUnique_List (New_String_Append old_string_list file_name).                                  
intros.                                 (* introduce inductive definition *)
induction old_string_list.              (* instantiate old_string_list into two cases *)
simpl.                                  
tauto.                                  (* prove true *)
simpl.                                  
simpl in H.                             
simpl in H0.                            
split.                                  (* split goal into two cases *)
destruct H0.                            (* break H0 down *)
destruct H.                             (* break H down *)
clear H1 H2 IHold_string_list.          (* clear hypothesis, but why? *)
induction old_string_list.              (* instantiate old_string_list into two cases *)
simpl.                                  
split.                                  (* split goal into two cases *)
intro.                                  (* same as hypothesis *)
apply H.                                (* ?? *)
symmetry.                               (* form t = u to u = t *)
assumption.                             (* type is equal to the goal *)
auto.                                   
simpl.                                  
simpl in H0.                            
destruct H0.                            (* break H0 down *)
split.                                  (* split goal into two cases *)
assumption.                             (* type is equal to the goal *)
apply IHold_string_list.                (* become the precondition *)
assumption.                             (* type is equal to the goal, H1 *)
apply IHold_string_list.                (* become the precondition *)
tauto.                                  (* ?? *)
tauto.                                  (* ?? *)
Qed.   

(* Proof: create operation doesn't violate the property that all filenames are unique *)
Lemma Check_Create : forall file_st file_name, Check_Filename_Unique file_st -> match FS_Create_Main file_name file_st with
                                    | None => True (* truncate fail means always true *)
                                    | Some new_st => Check_AllStringUnique_List (Return_All_Filename new_st)
                                  end. (* all filenames are unique after create operation *)
intros.
pose Create_File_AppendUnique.
specialize (y file_st file_name).
destruct (FS_Create_Main file_name file_st).
destruct y.
rewrite <- H1.
apply Check_CreatedString.
assumption.
assumption.
auto.
Qed.


(* delete a string from the current list of string *)
Fixpoint Delete_String_List (list_string : list string) (delete_name : string) : list string :=
  match list_string with
    | [] => []
    | hd::tl => if string_dec delete_name hd then tl
                                             else hd::Delete_String_List tl delete_name
  end.

(* Proof: delete operation doesn't change the existing file name in the file system *)
Lemma Delete_Doesnot_Change_Filename : forall file_st file_name, match FS_Delete_Main file_name file_st with
                                    | None => True (* delete fail means always true *)
                                    | Some new_st => Delete_String_List (Return_All_Filename file_st) file_name = Return_All_Filename new_st
                                  end. (* rest filenames doesn't change  *)
intros.
destruct file_st.
simpl.
induction fs_st0.
simpl.
auto.
simpl.
destruct a.
simpl.
destruct (string_dec file_name s).
reflexivity.
destruct (FS_Delete file_name fs_st0).
rewrite IHfs_st0.
reflexivity.
auto.
Qed.

(* Proof: a list of string still unique after delete one string *)
Lemma StringsUnique_AfterDelete : forall old_string_list file_name, Check_AllStringUnique_List old_string_list ->
                                                          Check_AllStringUnique_List (Delete_String_List old_string_list file_name).
intros.
induction old_string_list.
simpl.
auto.
simpl.
destruct (string_dec file_name a).
simpl in H.
destruct H.
assumption.
simpl.
split.
destruct n.
symmetry.


(* Proof: delete operation doesn't violate the property that all filenames are unique *)
Lemma Check_Delete : forall file_st file_name, Check_Filename_Unique file_st -> match FS_Delete_Main file_name file_st with
                                    | None => True (* truncate fail means always true *)
                                    | Some new_st => Check_AllStringUnique_List (Return_All_Filename new_st)
                                  end. (* all filenames are unique after delete operation *)
intros.
pose Delete_Doesnot_Change_Filename.
specialize (y file_st file_name).
destruct (FS_Delete_Main file_name file_st).
rewrite <- y. (* subgoal: Check_AllStringUnique_List(Delete_String_List (Return_All_Filename file_st) file_name) *)
simpl.

(*rename and delete are not ready*)
