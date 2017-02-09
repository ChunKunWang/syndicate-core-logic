Add LoadPath "/home/amos/applpi".
(** https://github.com/syndicate-storage/syndicate-core/blob/master/protobufs/sg.proto *)

Require Import libapplpi.
Require Import SG_applpi_string.

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
  { volume_id : String;
    owner_id : String;
    file_id : String;
    size : String}.

(** Definition of Syndicate requests from client *)
(* c.f. protobufs/sg.proto: l.80-94 *)
Inductive SG_req : Set :=
  | req_write : String -> SG_req
  | req_truncate: String -> SG_req
  | req_detach: String -> SG_req
  | req_rename: String -> SG_req
  | req_putchunks: String -> SG_req
  | req_deletechunks: String -> SG_req
  | req_setxattr: String -> SG_req
  | req_removexattr: String -> SG_req
  | req_reload: String -> SG_req
  | req_refresh: String -> SG_req
  | req_rename_hint: String -> SG_req.

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
  | resp_rename_hint : RespMsg.

Definition OutputStream := chan RespMsg true.

Definition ToFileSystem : Set := chan Manifest true.

Record SGstate : Set := sg_state
  {in_stream : InputStream;
   to_client : OutputStream;
(* Manifest info *)
   from_client : String;
(* file system is modeled as a process *)
   to_fs : ToFileSystem }.

Definition update_from (st : SGstate) (data: String) : SGstate := 
  sg_state (in_stream st) (to_client st)
  data (to_fs st).

Definition STATE : Set := SGstate.

Definition reply (r : RespMsg) (c : OutputStream) (cont : proc) : proc :=
  c << r >> cont.

Definition get_req (c : InputStream) (cont : SG_req -> proc) : proc :=
  c ?? cont.

Definition save_data (data : String) (st : STATE) (cont : proc) : proc :=
  let m := manifest (from_client st) data in to_fs st << m >> cont.

