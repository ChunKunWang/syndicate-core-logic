Add LoadPath "/home/amos/applpi".
(** https://github.com/syndicate-storage/syndicate-core/blob/master/protobufs/sg.proto *)

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import SG_fs.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.
Import ListNotations.

(** Result channel *)
Axiom result_chan : chan unit false.
Definition succ : proc := OutAtom result_chan tt.

(** Catch IO exception *)
Axiom IOexn_chan : chan unit false.
Definition IOexn := OutAtom IOexn_chan tt.

(** Catch a system failure *)
Axiom system_failure_chan : chan unit false.
Definition failure := OutAtom system_failure_chan tt.

Definition may_fail := nuP
  (fun x => parP (InAtom x)
    (parP (OutAtom x tt) (x ?? (fun _ => OutAtom system_failure_chan tt)))).

(** Manifest data plane *)
(* c.f. protobufs/sg.proto: l.44-60 *)
Record Manifest : Set := manifest
  { volume_id : string;
    owner_id : string;
    file_id : string;
    size : string}.

(** Definition of Syndicate requests from client *)
(* c.f. protobufs/sg.proto: l.80-94 *)
Inductive SG_req : Set :=
  | req_write : string -> nat -> bool -> SG_req
  | req_truncate: string -> nat -> SG_req
  | req_detach: string -> SG_req
  | req_rename: string -> string -> SG_req
  | req_putchunks: string -> SG_req
  | req_deletechunks: string -> SG_req
  | req_setxattr: string -> SG_req
  | req_removexattr: string -> SG_req
  | req_reload: string -> SG_req
  | req_refresh: string -> SG_req
  | req_rename_hint: string -> SG_req.

Record md_HTTP_connection_data : Set := con_data
  { header_message : SG_req}.

Definition InputStream : Set := chan SG_req true.

(** Response messages *)
Inductive RespMsg : Set :=
  | resp_write : RespMsg
  | resp_truncate : RespMsg
  | resp_detach : RespMsg
  | resp_rename : RespMsg
  | resp_putchunks : RespMsg
  | resp_deletechunks : RespMsg
  | resp_setxattr : RespMsg
  | resp_removexattr : RespMsg
  | resp_reload : RespMsg
  | resp_refresh : RespMsg
  | resp_rename_hint : RespMsg
  | resp_null : RespMsg.

Definition OutputStream := chan RespMsg true.

Record SGstate : Set := sg_state
  {in_stream : InputStream;
   to_client : OutputStream;
(* Manifest info *)
   from_client : Manifest;
(* file system is modeled as a process *)
   to_fs : FileSystemState }.

Definition update_from (st : SGstate) (data: Manifest) : SGstate := 
  sg_state (in_stream st) (to_client st)
  data (to_fs st).

Definition STATE : Set := SGstate.

Definition reply (r : RespMsg) (c : OutputStream) (cont : proc) : proc :=
  c << r >> cont.

Definition get_req (c : InputStream) (cont : SG_req -> proc) : proc :=
  c ?? cont.

(* a -> b -> c => a * b -> c*)

Definition sample_server (i:chan (nat * (chan nat true)) false) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in OutAtom r (plus a 1)).

Definition sample_client (i:chan (nat * (chan nat true)) false) (o:chan nat true) : proc :=
    nuPl (fun r => parP (OutAtom i (0,r)) (inP r (fun x => OutAtom o x))).

Definition sample_Run (i : chan (nat * (chan nat true)) false) (o : chan nat true) := 
  (parP (sample_server i) (sample_client i o)).


(* Server_v1/Client_v1
Definition server (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in 
                        match a with 
                          | con_data msg => match msg with
                                            | req_write request => OutAtom r resp_write
                                            | req_truncate request => OutAtom r resp_truncate
                                            | req_detach request => OutAtom r resp_detach
                                            | req_rename request => OutAtom r resp_rename
                                            | req_putchunks request => OutAtom r resp_putchunks
                                            | req_deletechunks request => OutAtom r resp_deletechunks
                                            | req_setxattr request => OutAtom r resp_setxattr
                                            | req_removexattr request => OutAtom r resp_removexattr
                                            | req_reload request => OutAtom r resp_reload
                                            | req_refresh request => OutAtom r resp_refresh
                                            | req_rename_hint request => OutAtom r resp_rename_hint
                                          end
                          end).

Definition client (req:md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) (o:chan RespMsg true) : proc :=
    nuPl (fun r => parP (OutAtom i (req,r)) (inP r (fun x => OutAtom o x))).

Definition Run (req:md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) (o:chan RespMsg true) := 
  (parP (server i) (client req i o)).
*)

(** Syndicate Server State: contain a list of SGstate as a logical time *)
Record SGServerState : Set := sg_server_st
  {server_st : list bool}.

Fixpoint Create_ServerState (SerStatus : bool) (server_st : list bool) : option (list bool) :=
  match server_st with
    | [] => Some [SerStatus]
    | hd::tl => match Create_ServerState SerStatus tl with
                  | None => None
                  | Some a => Some (hd::a)
                end
  end.

Definition Update_Server_State (server_status : bool) (SG_server : SGServerState) : option SGServerState :=
  match SG_server with
    | sg_server_st st => match Create_ServerState server_status st with
                          | None => None
                          | Some new => Some (sg_server_st new)
                        end
  end.

(* File System Request *)
Inductive FS_req : Set :=
  | freq_read: string -> nat -> FS_req
  | freq_write : string -> nat -> bool -> FS_req
  | freq_create: string -> FS_req
  | freq_delete: string -> FS_req
  | freq_rename: string -> string -> FS_req
  | freq_truncate: string -> nat -> FS_req
  | freq_null : FS_req.

(* File System Response *)
Inductive FSRespMsg : Set :=
  | fresp_read_ok : FSRespMsg
  | fresp_read_fail : FSRespMsg
  | fresp_write_ok : FSRespMsg
  | fresp_write_fail : FSRespMsg
  | fresp_create_ok : FSRespMsg
  | fresp_create_fail : FSRespMsg
  | fresp_delete_ok : FSRespMsg
  | fresp_delete_fail : FSRespMsg
  | fresp_rename_ok : FSRespMsg
  | fresp_rename_fail : FSRespMsg
  | fresp_truncate_ok : FSRespMsg
  | fresp_truncate_fail : FSRespMsg
  | fresp_null : FSRespMsg.

Definition Client (req:md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) (o:chan RespMsg true) : proc :=
    nuPl (fun r => parP (OutAtom i (req,r)) (inP r (fun x => OutAtom o x))).


Definition Server (i:chan (md_HTTP_connection_data * (chan RespMsg true)) false) 
                       (f_in: chan FS_req true)
                       (f_out: chan FSRespMsg true) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in 
                        match a with 
                          | con_data msg => match msg with
                                            | req_write req_fname req_offset req_content => 
                                                        outP f_in (freq_write req_fname req_offset req_content) 
                                                        (inP f_out (fun c => match c with
                                                                             | fresp_write_ok => OutAtom r resp_write
                                                                             | _ => OutAtom r resp_write
                                                                             end))
                                            | req_truncate req_fname req_len => 
                                                        outP f_in (freq_truncate req_fname req_len) 
                                                        (inP f_out (fun c => match c with
                                                                             | fresp_truncate_ok => OutAtom r resp_truncate
                                                                             | _ => OutAtom r resp_truncate
                                                                             end))
                                            | req_rename req_fname_old req_fname_new => 
                                                        outP f_in (freq_rename req_fname_old req_fname_new) 
                                                        (inP f_out (fun c => match c with
                                                                             | fresp_rename_ok => OutAtom r resp_rename
                                                                             | _ => OutAtom r resp_rename
                                                                             end))
                                            | _ => OutAtom r resp_null
                                          end
                          end).


Definition FS (f_in:chan FS_req false) (f_out:chan FSRespMsg true) (f_st:chan FileSystemState true) : proc :=
    rinP f_in (fun a => match a with 
                       | freq_read fname foffset => inP f_st (fun fst => match FS_Read_Main fname foffset fst with
                                                                | None => outP f_st fst (OutAtom f_out fresp_read_fail)
                                                                | Some new_st => outP f_st fst (OutAtom f_out fresp_read_ok)
                                                              end)
                       | freq_write fname foffset fcontent => inP f_st (fun fst => match FS_Write_Main fname foffset fcontent fst with
                                                                          | None => outP f_st fst (OutAtom f_out fresp_write_fail)
                                                                          | Some new_st => outP f_st new_st (OutAtom f_out fresp_write_ok)
                                                                        end)
                       | freq_create fname => inP f_st (fun fst => match FS_Create_Main fname fst with
                                                          | None => outP f_st fst (OutAtom f_out fresp_create_fail)
                                                          | Some new_st => outP f_st new_st (OutAtom f_out fresp_create_ok)
                                                        end)
                       | freq_delete fname => inP f_st (fun fst => match FS_Delete_Main fname fst with
                                                          | None => outP f_st fst (OutAtom f_out fresp_delete_fail)
                                                          | Some new_st => outP f_st new_st (OutAtom f_out fresp_delete_ok)
                                                        end)
                       | freq_rename old_fname new_fname => inP f_st (fun fst => match FS_Rename_Main old_fname new_fname fst with
                                                          | None => outP f_st fst (OutAtom f_out fresp_rename_fail)
                                                          | Some new_st => outP f_st new_st (OutAtom f_out fresp_rename_ok)
                                                        end)
                       | freq_truncate fname length => inP f_st (fun fst => match FS_Truncate_Main fname length fst with
                                                          | None => outP f_st fst (OutAtom f_out fresp_truncate_fail)
                                                          | Some new_st => outP f_st new_st (OutAtom f_out fresp_truncate_ok)
                                                        end)
                       | _ => OutAtom f_out fresp_null
                     end).




