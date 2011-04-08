(* ------------------------------------------------------------------------- *)
(* Memory safety for the H interface.                                        *)
(* ------------------------------------------------------------------------- *)

logfile "memory-def";;

(* Physical pages *)

new_type_abbrev("region_length",`:num`);;

new_type_abbrev("superpage_address",`:word10`);;

new_type_abbrev("superpage_offset",`:word10`);;

new_type_abbrev("physical_page_address",
                `:superpage_address # superpage_offset`);;

new_type_abbrev("offset",`:word12`);;

new_type_abbrev("page_data",`:offset -> byte`);;

(* Page directories *)

new_type_abbrev("page_directory_index",`:superpage_address`);;  (*** JEH ***)

let directory_contents_induct,directory_contents_recursion = define_type
    "directory_contents =
         Superpage superpage_address
       | Table physical_page_address";;

export_thm directory_contents_induct;;
export_thm directory_contents_recursion;;

new_type_abbrev("directory_page_data",
                `:page_directory_index -> directory_contents option`);;

(* Page tables *)

new_type_abbrev("page_table_index",`:superpage_offset`);;  (*** JEH ***)

new_type_abbrev("table_page_data",
                `:page_table_index -> physical_page_address option`);;

(* Pages *)

let page_induct,page_recursion = define_type
    "page = Environment page_data
          | Normal page_data
          | PageDirectory directory_page_data
          | PageTable table_page_data";;

export_thm page_induct;;
export_thm page_recursion;;

logfile "memory-thm";;

(* Physical pages *)

(* Page directories *)

let directory_contents_cases = prove_cases_thm directory_contents_induct;;

export_thm directory_contents_cases;;

let directory_contents_distinct = distinctness "directory_contents";;

export_thm directory_contents_distinct;;

let directory_contents_inj = injectivity "directory_contents";;

export_thm directory_contents_inj;;

(* Page tables *)

(* Pages *)

let page_cases = prove_cases_thm page_induct;;

export_thm page_cases;;

let page_distinct = distinctness "page";;

export_thm page_distinct;;

let page_inj = injectivity "page";;

export_thm page_inj;;

logfile_end ();;
