--
-- Natural Codes, algorithms adapted to PostgreSQL.
--
-- Original source at https://github.com/ppKrauss/SizedBigInt
--  and foundations at http://osm.codes/_foundations/art1.pdf

/* -----------
Copyright 2019, 2023 by ppkrauss and collaborators.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
   http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
------------- */


DROP SCHEMA IF EXISTS natcod CASCADE;
CREATE SCHEMA natcod;

-- -- --
-- Function name mnemonics parts:
--  hbig = hierarchical bigint;  vbit = varbit;
--  str = text with base n representation of vbit;
--  strbit = text of "0"s and "1"s, obtained by vbit::text.
--


-- Public LIB (adding or updating commom functions for general use)

CREATE or replace FUNCTION hex_to_varbit(h text) RETURNS varbit as $f$
 SELECT ('X' || $1)::varbit
$f$ LANGUAGE SQL IMMUTABLE;


CREATE or replace FUNCTION varbit_to_int( b varbit, blen int DEFAULT NULL) RETURNS int AS $f$
  -- slower  SELECT (  (b'0'::bit(32) || b) << COALESCE(blen,length(b))   )::bit(32)::int
  SELECT overlay( b'0'::bit(32) PLACING b FROM 33-COALESCE(blen,length(b)) )::int
$f$ LANGUAGE SQL IMMUTABLE;
-- select b'010101'::bit(32) left_copy, varbit_to_int(b'010101')::bit(32) right_copy;

CREATE or replace FUNCTION varbit_to_bigint( b varbit, blen int DEFAULT NULL) RETURNS bigint AS $f$
  SELECT overlay( b'0'::bit(64) PLACING b FROM 65-COALESCE(blen,length(b)) )::bigint
  -- litle bit less faster, SELECT ( (b'0'::bit(64) || b) << bit_length(b) )::bit(64)::bigint
$f$ LANGUAGE SQL IMMUTABLE;
-- select b'010101'::bit(64) left_copy, varbit_to_bigint(b'010101')::bit(64) right_copy;


-- -- CONVERT:

CREATE FUNCTION natcod.hbig_to_vbit(x bigint) RETURNS varbit as $f$  -- hb_decode
  SELECT substring( x_bin from 1+position(B'1' in x_bin) )
  FROM (select x::bit(64)) t(x_bin) -- WHERE $1>7 AND $1<4611686018427387904
$f$ LANGUAGE SQL IMMUTABLE;
COMMENT ON FUNCTION natcod.hbig_to_vbit
  IS 'Converts hiherarchical Bigint (hbig), representing hidden-bit Natural Code, into varbit.'
;

CREATE FUNCTION natcod.vbit_to_hbig(x varbit) RETURNS bigint as $f$  -- hb_encode
  SELECT overlay( b'0'::bit(64) PLACING (b'1' || x) FROM 64-length(x) )::bigint
$f$ LANGUAGE SQL IMMUTABLE;
COMMENT ON FUNCTION natcod.vbit_to_hbig(varbit)
  IS 'Converts varbit into a Bigint representing hidden-bit (hb) Natural Code.'
;


CREATE FUNCTION natcod.strbit_to_vbit(b text, p_len int DEFAULT null) RETURNS varbit AS $f$
   SELECT CASE WHEN p_len>0 THEN  lpad(b, p_len, '0')::varbit ELSE  b::varbit  END
$f$  LANGUAGE SQL IMMUTABLE;

CREATE FUNCTION natcod.bitlen_of(x bigint) RETURNS int as $f$
  SELECT 64-position(B'1' in x::bit(64))
$f$ LANGUAGE SQL IMMUTABLE;

-- -- GENERATE SERIES:

CREATE FUNCTION natcod.generatep_hb_series(bit_len int) RETURNS setof bigint as $f$
  SELECT i::bigint | maxval as x
  FROM (SELECT (2^bit_len)::bigint) t(maxval),
       LATERAL generate_series(0,maxval-1) s(i)
$f$ LANGUAGE SQL IMMUTABLE;
COMMENT ON FUNCTION natcod.generatep_hb_series
  IS 'Obtain a sequency of hidden-bit Natural Codes P set (fixed length), from zero to 2^bit_len-1.'
;

CREATE FUNCTION natcod.generate_hb_series(bit_len int) RETURNS setof bigint as $f$
-- See optimized at https://stackoverflow.com/q/75503880/287948
DECLARE
  s text;
BEGIN
  s := 'SELECT * FROM natcod.generatep_hb_series(1)';
  FOR i IN 2..bit_len LOOP
    s := s || ' UNION ALL  SELECT * FROM natcod.generatep_hb_series('|| i::text ||')';
  END LOOP;
  RETURN QUERY EXECUTE s;
END;
$f$ LANGUAGE PLpgSQL IMMUTABLE;

CREATE FUNCTION natcod.generate_vbit_series(bit_len int) RETURNS setof varbit as $f$
  SELECT natcod.hbig_to_vbit(hb)
  FROM natcod.generate_hb_series($1) t(hb) ORDER BY 1
$f$ LANGUAGE SQL IMMUTABLE;


------
------ BASE CONVERT
------

CREATE FUNCTION natcod.vbit_to_baseh(
  p_val varbit,  -- input
  p_base int DEFAULT 4 -- selecting base2h, base4h, base8h, or base16h.
) RETURNS text AS $f$
DECLARE
    vlen int;
    pos0 int;
    ret text := '';
    blk varbit;
    blk_n int;
    bits_per_digit int;
    tr int[] := '{ {1,2,0,0}, {1,3,4,0}, {1,3,5,6} }'::int[]; -- --4h(bits,pos), 8h(bits,pos)
    tr_selected JSONb;
    trtypes JSONb := '{"2":[1,1], "4":[1,2], "8":[2,3], "16":[3,4]}'::JSONb; -- TrPos,bits. Can be array.
    trpos int;
    baseh "char"[] := array[ -- new 2023 standard for Baseh:
      '[0:15]={G,Q,x,x,x,x,x,x,x,x,x,x,x,x,x,x}'::"char"[], --1. 1 bit in 4h,8h,16h
      '[0:15]={0,1,2,3,x,x,x,x,x,x,x,x,x,x,x,x}'::"char"[], --2. 2 bits in 4h
      '[0:15]={H,M,R,V,x,x,x,x,x,x,x,x,x,x,x,x}'::"char"[], --3. 2 bits 8h,16h
      '[0:15]={0,1,2,3,4,5,6,7,x,x,x,x,x,x,x,x}'::"char"[], --4. 3 bits in 8h
      '[0:15]={J,K,N,P,S,T,Z,Y,x,x,x,x,x,x,x,x}'::"char"[], --5. 3 bits in 16h
      '[0:15]={0,1,2,3,4,5,6,7,8,9,a,b,c,d,e,f}'::"char"[]  --6. 4 bits in 16h
    ]; -- jumpping I,O and L,U,W,X letters!
       -- the standard alphabet is https://tools.ietf.org/html/rfc4648#section-6
BEGIN
  vlen := bit_length(p_val);
  tr_selected := trtypes->(p_base::text);  -- can be array instead of JSON
  IF p_val IS NULL OR tr_selected IS NULL OR vlen=0 THEN
    RETURN NULL; -- or  p_retnull;
  END IF;
  IF p_base=2 THEN
    RETURN $1::text; --- direct bit string as string
  END IF;
  bits_per_digit := (tr_selected->>1)::int;
  blk_n := vlen/bits_per_digit;
  pos0  := (tr_selected->>0)::int;
  trpos := tr[pos0][bits_per_digit];
  FOR counter IN 1..blk_n LOOP
      blk := substring(p_val FROM 1 FOR bits_per_digit);
      ret := ret || baseh[trpos][ varbit_to_int(blk,bits_per_digit) ];
      p_val := substring(p_val FROM bits_per_digit+1); -- same as p_val<<(bits_per_digit*blk_n)
  END LOOP;
  vlen := bit_length(p_val);
  IF p_val!=b'' THEN -- vlen % bits_per_digit>0
    trpos := tr[pos0][vlen];
    ret := ret || baseh[trpos][ varbit_to_int(p_val,vlen) ];
  END IF;
  RETURN ret;
END
$f$ LANGUAGE plpgsql IMMUTABLE;
COMMENT ON FUNCTION natcod.vbit_to_baseh
  IS 'Converts bit string to text, using base2h, base4h, base8h or base16h. Uses letters "G" and "H" to sym44bolize non strandard bit strings (0 for44 bases44). Uses extended alphabet (with no letter I,O,U W or X) for base8h and base16h.'
;

CREATE FUNCTION natcod.vbit_to_strstd(
  p_val varbit,  -- input
  p_base text DEFAULT '4js' -- selecting base2js? base4js, etc. with no leading zeros.
) RETURNS text AS $f$
DECLARE
    vlen int;
    pos0 int;
    ret text := '';
    blk varbit;
    blk_n int;
    bits_per_digit int;
    trtypes JSONb := '{
      "4js":[0,1,2],"8js":[0,1,3],"16js":[0,1,4],
      "32ghs":[1,4,5],"32hex":[1,1,5],"32nvu":[1,2,5],"32rfc":[1,3,5],
      "64url":[2,8,6]
    }'::JSONb; -- var,pos,bits
    base0 "char"[] := array[
      '[0:15]={0,1,2,3,4,5,6,7,8,9,a,b,c,d,e,f}'::"char"[] --1. 4,5,16 js
    ];
    base1 "char"[] := array[
       '[0:31]={0,1,2,3,4,5,6,7,8,9,a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v}'::"char"[] --1=32hex
      ,'[0:31]={0,1,2,3,4,5,6,7,8,9,B,C,D,F,G,H,J,K,L,M,N,P,Q,R,S,T,U,V,W,X,Y,Z}'::"char"[] --2=32nvu
      ,'[0:31]={A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,Q,R,S,T,U,V,W,X,Y,Z,2,3,4,5,6,7}'::"char"[] --3=32rfc
      ,'[0:31]={0,1,2,3,4,5,6,7,8,9,b,c,d,e,f,g,h,j,k,m,n,p,q,r,s,t,u,v,w,x,y,z}'::"char"[] --4=32ghs
    ];
    -- "64url": "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
    tr_selected JSONb;
    trbase "char"[];
BEGIN
  vlen := bit_length(p_val);
  tr_selected := trtypes->(p_base::text);-- [1=var,2=pos,3=bits]
  IF p_val IS NULL OR tr_selected IS NULL OR vlen=0 THEN
    RETURN NULL; -- or  p_retnull;
  END IF;
  IF p_base='2' THEN
     -- need to strip leading zeros
    RETURN $1::text; --- direct bit string as string
  END IF;
  bits_per_digit := (tr_selected->>2)::int;
  IF vlen % bits_per_digit != 0 THEN
    RETURN NULL;  -- trigging ERROR
  END IF;
  blk_n := vlen/bits_per_digit;
  pos0 = (tr_selected->>1)::int;
  -- trbase := CASE tr_selected->>0 WHEN '0' THEN base0[pos0] ELSE base1[pos0] END; -- NULL! pgBUG?
  trbase := CASE tr_selected->>0 WHEN '0' THEN base0 ELSE base1 END;
  --RAISE NOTICE 'HELLO: %; % % -- %',pos0,blk_n,trbase,trbase[pos0][1];
  FOR counter IN 1..blk_n LOOP
      blk := substring(p_val FROM 1 FOR bits_per_digit);
      ret := ret || trbase[pos0][ varbit_to_int(blk,bits_per_digit) ];
      p_val := substring(p_val FROM bits_per_digit+1);
  END LOOP;
  vlen := bit_length(p_val);
  -- IF p_val!=b'' THEN ERROR
  RETURN ret;
END
$f$ LANGUAGE PLpgSQL IMMUTABLE;
COMMENT ON FUNCTION natcod.vbit_to_strstd
 IS 'Converts bit string to text, using standard numeric bases (base4js, base32ghs, etc.).'
;

/**
 * Hub function to base conversion. Varbit to String.
 */
CREATE FUNCTION natcod.vbit_to_str(
  p_val varbit,  -- input
  p_base text DEFAULT '4h'
) RETURNS text AS $f$
  SELECT CASE WHEN x IS NULL OR p_val IS NULL THEN NULL
    WHEN x[1] IS NULL THEN  natcod.vbit_to_strstd(p_val, x[2])
    ELSE  natcod.vbit_to_baseh(p_val, x[1]::int)  END
  FROM regexp_match(lower(p_base), '^(?:base\-?\s*)?(?:(\d+)h|(\d.+))$') t(x);
$f$ LANGUAGE SQL IMMUTABLE;
--  select natcod.vbit_to_str(b'011010'), natcod.vbit_to_str(b'011010','16h'), natcod.vbit_to_str(b'000111','4js');


CREATE FUNCTION natcod.strbh_to_vbit(
  p_val text,  -- input
  p_base int DEFAULT 4 -- selecting base2h, base4h, base8h, or base16h.
) RETURNS varbit AS $f$
DECLARE
  tr_hdig jsonb := '{
    "G":[1,0],"H":[1,1],
    "J":[2,0],"K":[2,1],"L":[2,2],"M":[2,3],
    "N":[3,0],"P":[3,1],"Q":[3,2],"R":[3,3],
    "S":[3,4],"T":[3,5],"V":[3,6],"Z":[3,7]
  }'::jsonb;
  tr_full jsonb := '{
    "0":0,"1":1,"2":2,"3":3,"4":4,"5":5,"6":6,"7":7,"8":8,
    "9":9,"a":10,"b":11,"c":12,"d":13,"e":14,"f":15
  }'::jsonb;
  blk text[];
  bits varbit;
  n int;
  i char;
  ret varbit;
  BEGIN
  ret = '';
  blk := regexp_match(p_val,'^([0-9a-f]*)([GHJ-NP-TVZ])?$');
  IF blk[1] >'' THEN
    FOREACH i IN ARRAY regexp_split_to_array(blk[1],'') LOOP
      ret := ret || CASE p_base
        WHEN 16 THEN (tr_full->>i)::int::bit(4)::varbit
        WHEN 8 THEN (tr_full->>i)::int::bit(3)::varbit
        WHEN 4 THEN (tr_full->>i)::int::bit(2)::varbit
        END;
    END LOOP;
  END IF;
  IF blk[2] >'' THEN
    n = (tr_hdig->blk[2]->>0)::int;
    ret := ret || CASE n
      WHEN 1 THEN (tr_hdig->blk[2]->>1)::int::bit(1)::varbit
      WHEN 2 THEN (tr_hdig->blk[2]->>1)::int::bit(2)::varbit
      WHEN 3 THEN (tr_hdig->blk[2]->>1)::int::bit(3)::varbit
      END;
  END IF;
  RETURN ret;
  END
$f$ LANGUAGE PLpgSQL IMMUTABLE;
-- select natcod.strbh_to_vbit('f3V',16);


CREATE FUNCTION natcod.str_to_vbit(
  p_val text,  -- input
  p_base text DEFAULT '4h' -- selecting base2h, base4h, base8h, or base16h.
) RETURNS varbit AS $f$
DECLARE
  parts text[];
  base int;
  info jsonb;
  tr_full jsonb;
  blk text[];
  ch char;
  ret varbit;
BEGIN
  parts := regexp_match(lower(p_base),'^(?:base\-?|b\-?)?(([0-9]+)([^0-9].*)?)$');
  IF parts IS NULL OR NOT(parts[2]>'0') THEN
    RETURN NULL;
  ELSE
    base := parts[2]::int;
    IF parts[3]='h' AND base IN (4,8,16) THEN
      RETURN natcod.strbh_to_vbit(p_val,base);
    ELSE  -- get definition, validate and solve
      info := natcod.jinfo_term(parts[1],'base_label');
      IF info IS NULL OR NOT(info?'kx_tr') OR base!=(info->>'base')::int THEN
        RETURN NULL;
      ELSE
        tr_full := info->'kx_tr';
        blk := regexp_match( p_val, info->>'regex' ); -- validate
        -- RAISE NOTICE ' val=%, regex=%, %', p_val, info->>'regex',blk::text;
        ret := '';
        IF blk[1] >'' THEN
          FOREACH ch IN ARRAY regexp_split_to_array(blk[1],'') LOOP
            ret := ret || CASE base
              WHEN 64 THEN (tr_full->>ch)::int::bit(6)::varbit
              WHEN 32 THEN (tr_full->>ch)::int::bit(5)::varbit
              WHEN 16 THEN (tr_full->>ch)::int::bit(4)::varbit
              WHEN 8 THEN (tr_full->>ch)::int::bit(3)::varbit
              WHEN 4 THEN (tr_full->>ch)::int::bit(2)::varbit
              END;
          END LOOP;
        ELSE
          -- RAISE NOTICE ' val=%, regex=%', p_val, info->>'regex';
          return NULL; --b'011'::varbit;
        END IF;
        RETURN ret;
      END IF; -- info
    END IF; -- parts[3]
  END IF; -- parts  null
END
$f$ LANGUAGE PLpgSQL IMMUTABLE;
-- SELECT natcod.str_to_vbit('f3V','16h'), natcod.str_to_vbit('f3','16js');

---------------------------
---------------------------

CREATE FUNCTION natcod.vbit_to_hbig(p text) RETURNS bigint AS $wrap$
  SELECT natcod.vbit_to_hbig(p::varbit)
$wrap$ LANGUAGE SQL IMMUTABLE;
COMMENT ON FUNCTION natcod.vbit_to_hbig(text)
  IS 'A wrap for vbit_to_hbig(varbit).'
;


CREATE FUNCTION natcod.hbig_to_str(
  p_val bigint,  -- input
  p_base text DEFAULT '4h'
) RETURNS text AS $wrap$
  SELECT natcod.vbit_to_str(natcod.hbig_to_vbit($1),$2)
$wrap$ LANGUAGE SQL IMMUTABLE;
-- select natcod.hbig_toString(7999999999999949993,'16h'), natcod.hbig_toString(80,'4h');

--------

CREATE FUNCTION natcod.num_base_decode(
  p_val text,
  p_base int, -- from 2 to 36
  p_alphabet text = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'
) RETURNS numeric(500,0) AS $f$
		  SELECT SUM(
	       ( p_base::numeric(500,0)^(length($1)-i) )::numeric(500,0)
	       *   -- base^j * digit_j
	       ( strpos(p_alphabet,d) - 1 )::numeric(500,0)
	    )::numeric(500,0) --- returns numeric?
  		FROM regexp_split_to_table($1,'') WITH ORDINALITY t1(d,i)
$f$ LANGUAGE SQL IMMUTABLE;
