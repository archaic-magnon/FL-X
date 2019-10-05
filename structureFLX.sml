use "signatureFLX.sml";

structure Flx : FLX =
  	struct

  		(*define all exception*)
	   	exception Not_wellformed;
	    exception Not_nf;
	    exception Not_int;

	    (*define datatype*)
    	datatype term = VAR of string (* variable *)
          | Z           (* zero *)
          | T           (* true *)
          | F           (* false *)
          | P of term   (* Predecessor *)
          | S of term   (* Successor *)
          | ITE of term * term * term   (* If then else *)
          | IZ of term  (* is zero *)
          | GTZ of term (* is greater than zero *)


		(*check for valid nf integer start at S*)
		fun isIntegerS Z = true
			| isIntegerS (S n) = isIntegerS n
			| isIntegerS t = false

		(*check for valid nf integer start at P*)
		fun isIntegerP Z = true
			| isIntegerP (P n) = isIntegerP n
			| isIntegerP t = false

		(*check for valid nf integer*)
		fun isInteger Z = true
			| isInteger (S n) = isIntegerS (S n)
			| isInteger (P n) = isIntegerP(P n)
			| isInteger t = false

		(*check for valid integer not necessary nf*)
		fun isReallyInteger Z = true
			| isReallyInteger (S n) = isReallyInteger n
			| isReallyInteger (P n) = isReallyInteger n
			| isReallyInteger t = false



		(*output term1/term2 of ite*)
		fun scan1([], bc, term_string) = raise Not_wellformed
			| scan1(l as h::t, bc, term_string) = 
				if(h = #"," andalso bc = 0 andalso term_string<> []) then ( String.implode(List.rev(term_string)), t)
				else if(h = #"," andalso bc = 0 andalso term_string =  []) then raise Not_wellformed
				else if(h = #"(") then scan1(t, bc+1, h::term_string)
				else if(h = #")") then scan1(t, bc-1, h::term_string)
				else scan1(t, bc, h::term_string)

		(*output term3 of ite*)
		fun scan3([], bc, []) = raise Not_wellformed
			| scan3([], bc, term_string as a::b) = if (bc = 0) then String.implode(List.rev(term_string)) else raise Not_wellformed
			| scan3(l as h::t, bc, term_string) = 
				if(h = #"(") then scan3(t, bc+1, h::term_string)
				else if(h = #")") then scan3(t, bc-1, h::term_string)
				else scan3(t, bc, h::term_string)

		(*convert input string to term*)
		fun fromString "" = raise Not_wellformed
			| fromString "Z" = Z
			| fromString "T" = T
			| fromString "F" = F
			| fromString s = 
				if(String.isPrefix (" ") s) then fromString(String.substring(s, 1, (String.size s) - 1) )
				else if(String.isPrefix ("(S ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 4;
						val start_index = 3;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(S (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(P ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 4;
						val start_index = 3;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(P (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(IZ ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 5;
						val start_index = 4;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(IZ (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(GTZ ") s  andalso String.isSuffix (")") s ) then
					let
						val s_len = String.size s;
						val remaining_len = s_len - 6;
						val start_index = 5;
						val remaining_str = String.substring(s, start_index, remaining_len);
					in
						(GTZ (fromString(remaining_str)))
					end

				else if(String.isPrefix ("(ITE <") s  andalso String.isSuffix (">)") s ) then
					let

						val s_len = String.size s;
						val remaining_len = s_len - 8;
						val start_index = 6;
						val remaining_str = String.substring(s, start_index, remaining_len);


						val (term1_string, r1) = scan1( String.explode(remaining_str), 0, []);
						val (term2_string, r2) = scan1( r1, 0, []);
						val term3_string = scan3( r2, 0, []);

						val t1_term = fromString(term1_string);
						val t2_term = fromString(term2_string);
						val t3_term = fromString(term3_string);


					in
						(ITE(t1_term,t2_term,t3_term))
					end

				else if(List.all Char.isLower (explode s)) then
					VAR(s)

				else raise  Not_wellformed

		
		

		(*convert integer to term*)
		fun fromInt 0 = Z
			| fromInt n = 
				if(n > 0) then S(fromInt (n-1))
				else P(fromInt (n+1))

		(*convert term to integer*)
		fun toInt Z = 0
			| toInt (S (P t:term)) = if(isReallyInteger t) then raise Not_nf else raise Not_int
			| toInt (P (S t:term)) = if(isReallyInteger t) then raise Not_nf else raise Not_int
			| toInt (S t:term) = if(isReallyInteger t) then (1 + toInt(t)) else raise Not_int
			| toInt (P t:term) = if(isReallyInteger t) then (~1 + toInt(t)) else raise Not_int
			| toInt n  = raise Not_int

		(*convert term to string*)
		fun toString (VAR x) = x
			| toString Z = "Z"
			| toString T = "T"
			| toString F = "F"
			| toString (S t) = "(S " ^ toString(t) ^ ")"
			| toString (P t) = "(P " ^ toString(t) ^ ")"
			| toString (ITE(b, x, y)) = "(ITE <" ^ toString(b) ^ "," ^ toString(x) ^ "," ^toString(y) ^ ">)"
			| toString(IZ t) = "(IZ " ^ toString(t) ^ ")"
			| toString(GTZ t) = "(GTZ " ^ toString(t) ^ ")"


		(*normalize term*)
		fun normalize (VAR x) = (VAR x)
			| normalize Z = Z
			| normalize (S t) = 
				let 
					val nft = normalize t;
				in
					(case nft of 
						Z => S Z
						| S nft' => S nft
						| P nft' => nft'
						| _ => (S nft)

					)
				end
			| normalize (P t) = 
				let 
					val nft = normalize t;
				in
					(case nft of 
						Z => P Z
						| S nft' => nft'
						| P nft' => P nft
						| _ => (P nft)
					)
				end
			| normalize T = T
			| normalize F = F
			| normalize (ITE(b, x, y)) = 
				let
					val nb = normalize(b);
					val nx = normalize(x);
					val ny = normalize(y);
				in
					if(nx = ny) then nx
					else 
						(case nb of 
							T => nx
							| F => ny
							| _ => (ITE(nb, nx, ny))
						)
				end
			| normalize (IZ Z) = T
			| normalize (IZ t) = 
				let
					val nt = normalize(t);
					val is_int = isInteger nt;
				in
					if(is_int) then
						(case nt of 
							S n => F
							| P n => F
							| Z => T
							| _ => (IZ nt)
						)
					else
						(IZ nt)
				end
			| normalize (GTZ Z) = F
			| normalize (GTZ t) = 
				let
					val nt = normalize(t);
					val is_int = isInteger nt;
				in
					if(is_int) then
						(case nt of 
							S n => T
							| P n => F
							| Z => F
							| _ => (GTZ nt)
						)
					else
						(GTZ nt)
				end
	end