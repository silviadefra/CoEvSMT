(set-logic QF_LIA)
(declare-const c_main_~x~2 Int)
(declare-const c_main_~y~2 Int)
(declare-const c_main_~N~2 Int)
(assert true)
(assert true)
(assert true)
(assert true)
(declare-const |v_main_#res_1_const_385270467| Int)
(assert (let ((|v_main_#res_1| |v_main_#res_1_const_385270467|)) (= |v_main_#res_1| 0)))
(assert true)
(declare-const v_main_~x~2_1_const_-1298215918 Int)
(declare-const v_main_~y~2_1_const_-1297288047 Int)
(assert (let ((v_main_~x~2_1 v_main_~x~2_1_const_-1298215918) (v_main_~y~2_1 v_main_~y~2_1_const_-1297288047)) (not (>= (+ v_main_~x~2_1 v_main_~y~2_1) 0))))
(declare-const v_main_~x~2_2_const_-1298215919 Int)
(declare-const v_main_~N~2_1_const_-1337006212 Int)
(assert (let ((v_main_~x~2_2 v_main_~x~2_2_const_-1298215919) (v_main_~N~2_1 v_main_~N~2_1_const_-1337006212)) (not (<= v_main_~x~2_2 v_main_~N~2_1))))
(declare-const v_main_~x~2_3_const_-1298215920 Int)
(declare-const v_main_~N~2_2_const_-1337006213 Int)
(assert (let ((v_main_~x~2_3 v_main_~x~2_3_const_-1298215920) (v_main_~N~2_2 v_main_~N~2_2_const_-1337006213)) (<= v_main_~x~2_3 v_main_~N~2_2)))
(declare-const v_main_~x~2_4_const_-1298215889 Int)
(declare-const |v_main_#t~nondet0_2_const_-425629150| Int)
(declare-const v_main_~y~2_2_const_-1297288048 Int)
(declare-const |v_main_#t~nondet1_2_const_-425630111| Int)
(declare-const v_main_~N~2_3_const_-1337006214 Int)
(declare-const |v_main_#t~nondet2_2_const_-425631072| Int)
(assert
 (let
 ((v_main_~x~2_4 v_main_~x~2_4_const_-1298215889)
  (|v_main_#t~nondet0_2| |v_main_#t~nondet0_2_const_-425629150|)
  (v_main_~y~2_2 v_main_~y~2_2_const_-1297288048)
  (|v_main_#t~nondet1_2| |v_main_#t~nondet1_2_const_-425630111|)
  (v_main_~N~2_3 v_main_~N~2_3_const_-1337006214)
  (|v_main_#t~nondet2_2| |v_main_#t~nondet2_2_const_-425631072|))
 (and (= v_main_~x~2_4 |v_main_#t~nondet0_2|)
 (= v_main_~y~2_2 |v_main_#t~nondet1_2|)
 (= v_main_~N~2_3 |v_main_#t~nondet2_2|))))
(declare-const v_main_~N~2_4_const_-1337006215 Int)
(declare-const v_main_~x~2_5_const_-1298215890 Int)
(declare-const v_main_~y~2_3_const_-1297288017 Int)
(declare-const |v_main_#res_2_const_385270466| Int)
(assert
 (let
 ((v_main_~N~2_4 v_main_~N~2_4_const_-1337006215)
  (v_main_~x~2_5 v_main_~x~2_5_const_-1298215890)
  (v_main_~y~2_3 v_main_~y~2_3_const_-1297288017)
  (|v_main_#res_2| |v_main_#res_2_const_385270466|))
 (and
 (or (>= v_main_~N~2_4 536870912)
 (>= v_main_~x~2_5 536870912)
 (>= v_main_~y~2_3 536870912)
 (< v_main_~x~2_5 (- 1073741824)))
 (= |v_main_#res_2| 0))))
(declare-const v_main_~N~2_5_const_-1337006216 Int)
(declare-const v_main_~x~2_6_const_-1298215891 Int)
(declare-const v_main_~y~2_4_const_-1297288018 Int)
(assert
 (let
 ((v_main_~N~2_5 v_main_~N~2_5_const_-1337006216)
  (v_main_~x~2_6 v_main_~x~2_6_const_-1298215891)
  (v_main_~y~2_4 v_main_~y~2_4_const_-1297288018))
 (not
 (or (>= v_main_~N~2_5 536870912)
 (>= v_main_~x~2_6 536870912)
 (>= v_main_~y~2_4 536870912)
 (< v_main_~x~2_6 (- 1073741824))))))
(declare-const v_main_~x~2_8_const_-1298215893 Int)
(declare-const v_main_~y~2_6_const_-1297288020 Int)
(declare-const v_main_~x~2_7_const_-1298215892 Int)
(declare-const |v_main_#t~nondet3_2_const_-425615617| Int)
(declare-const v_main_~y~2_5_const_-1297288019 Int)
(assert
 (let
 ((v_main_~x~2_8 v_main_~x~2_8_const_-1298215893)
  (v_main_~y~2_6 v_main_~y~2_6_const_-1297288020)
  (v_main_~x~2_7 v_main_~x~2_7_const_-1298215892)
  (|v_main_#t~nondet3_2| |v_main_#t~nondet3_2_const_-425615617|)
  (v_main_~y~2_5 v_main_~y~2_5_const_-1297288019))
 (and (not (= |v_main_#t~nondet3_2| 0))
 (= v_main_~x~2_7 (+ (* 2 v_main_~x~2_8) v_main_~y~2_6))
 (= v_main_~y~2_5 (+ v_main_~y~2_6 1)))))
(declare-const v_main_~x~2_9_const_-1298215894 Int)
(declare-const v_main_~x~2_10_const_-1587824580 Int)
(declare-const |v_main_#t~nondet3_4_const_-425615619| Int)
(assert
 (let
 ((v_main_~x~2_9 v_main_~x~2_9_const_-1298215894)
  (v_main_~x~2_10 v_main_~x~2_10_const_-1587824580)
  (|v_main_#t~nondet3_4| |v_main_#t~nondet3_4_const_-425615619|))
 (and (= |v_main_#t~nondet3_4| 0) (= v_main_~x~2_9 (+ v_main_~x~2_10 1)))))
(declare-const v_main_~x~2_11_const_-1587824581 Int)
(declare-const v_main_~y~2_7_const_-1297288021 Int)
(assert
 (let
 ((v_main_~x~2_11 v_main_~x~2_11_const_-1587824581)
  (v_main_~y~2_7 v_main_~y~2_7_const_-1297288021))
 (>= (+ v_main_~x~2_11 v_main_~y~2_7) 0)))
(assert false)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(declare-const v_main_~N~2_6_const_-1337006217 Int)
(declare-const v_main_~x~2_12_const_-1587824582 Int)
(declare-const v_main_~y~2_8_const_-1297288022 Int)
(declare-const |v_main_#t~nondet0_4_const_-425629152| Int)
(declare-const |v_main_#t~nondet1_4_const_-425630081| Int)
(declare-const |v_main_#t~nondet2_4_const_-425631042| Int)
(assert
 (let
 ((v_main_~N~2_6 v_main_~N~2_6_const_-1337006217)
  (v_main_~x~2_12 v_main_~x~2_12_const_-1587824582)
  (v_main_~y~2_8 v_main_~y~2_8_const_-1297288022)
  (|v_main_#t~nondet0_4| |v_main_#t~nondet0_4_const_-425629152|)
  (|v_main_#t~nondet1_4| |v_main_#t~nondet1_4_const_-425630081|)
  (|v_main_#t~nondet2_4| |v_main_#t~nondet2_4_const_-425631042|))
 (and (not (>= (+ v_main_~x~2_12 v_main_~y~2_8) 0))
 (not
 (or (>= v_main_~N~2_6 536870912)
 (>= v_main_~x~2_12 536870912)
 (>= v_main_~y~2_8 536870912)
 (< v_main_~x~2_12 (- 1073741824))))
 (= v_main_~x~2_12 |v_main_#t~nondet0_4|)
 (= v_main_~y~2_8 |v_main_#t~nondet1_4|)
 (= v_main_~N~2_6 |v_main_#t~nondet2_4|))))
(declare-const v_main_~N~2_7_const_-1337006218 Int)
(declare-const v_main_~x~2_13_const_-1587824583 Int)
(declare-const v_main_~y~2_9_const_-1297288023 Int)
(declare-const |v_main_#t~nondet0_6_const_-425629122| Int)
(declare-const |v_main_#t~nondet1_6_const_-425630083| Int)
(declare-const |v_main_#t~nondet2_6_const_-425631044| Int)
(assert
 (let
 ((v_main_~N~2_7 v_main_~N~2_7_const_-1337006218)
  (v_main_~x~2_13 v_main_~x~2_13_const_-1587824583)
  (v_main_~y~2_9 v_main_~y~2_9_const_-1297288023)
  (|v_main_#t~nondet0_6| |v_main_#t~nondet0_6_const_-425629122|)
  (|v_main_#t~nondet1_6| |v_main_#t~nondet1_6_const_-425630083|)
  (|v_main_#t~nondet2_6| |v_main_#t~nondet2_6_const_-425631044|))
 (and (not (>= (+ v_main_~x~2_13 v_main_~y~2_9) 0))
 (not
 (or (>= v_main_~N~2_7 536870912)
 (>= v_main_~x~2_13 536870912)
 (>= v_main_~y~2_9 536870912)
 (< v_main_~x~2_13 (- 1073741824))))
 (= v_main_~x~2_13 |v_main_#t~nondet0_6|)
 (= v_main_~y~2_9 |v_main_#t~nondet1_6|)
 (= v_main_~N~2_7 |v_main_#t~nondet2_6|))))
(declare-const v_main_~N~2_8_const_-1337006219 Int)
(declare-const v_main_~x~2_14_const_-1587824584 Int)
(declare-const v_main_~y~2_10_const_-1559322787 Int)
(declare-const |v_main_#t~nondet0_8_const_-425629124| Int)
(declare-const |v_main_#t~nondet1_8_const_-425630085| Int)
(declare-const |v_main_#t~nondet2_8_const_-425631046| Int)
(assert
 (let
 ((v_main_~N~2_8 v_main_~N~2_8_const_-1337006219)
  (v_main_~x~2_14 v_main_~x~2_14_const_-1587824584)
  (v_main_~y~2_10 v_main_~y~2_10_const_-1559322787)
  (|v_main_#t~nondet0_8| |v_main_#t~nondet0_8_const_-425629124|)
  (|v_main_#t~nondet1_8| |v_main_#t~nondet1_8_const_-425630085|)
  (|v_main_#t~nondet2_8| |v_main_#t~nondet2_8_const_-425631046|))
 (and (>= (+ v_main_~x~2_14 v_main_~y~2_10) 0)
 (not
 (or (>= v_main_~N~2_8 536870912)
 (>= v_main_~x~2_14 536870912)
 (>= v_main_~y~2_10 536870912)
 (< v_main_~x~2_14 (- 1073741824))))
 (= v_main_~x~2_14 |v_main_#t~nondet0_8|)
 (= v_main_~y~2_10 |v_main_#t~nondet1_8|)
 (= v_main_~N~2_8 |v_main_#t~nondet2_8|))))
(declare-const v_main_~N~2_9_const_-1337006220 Int)
(declare-const v_main_~x~2_15_const_-1587824585 Int)
(declare-const v_main_~y~2_11_const_-1559322788 Int)
(declare-const |v_main_#t~nondet0_10_const_-311470069| Int)
(declare-const |v_main_#t~nondet1_10_const_-311450644| Int)
(declare-const |v_main_#t~nondet2_10_const_-311546035| Int)
(assert
 (let
 ((v_main_~N~2_9 v_main_~N~2_9_const_-1337006220)
  (v_main_~x~2_15 v_main_~x~2_15_const_-1587824585)
  (v_main_~y~2_11 v_main_~y~2_11_const_-1559322788)
  (|v_main_#t~nondet0_10| |v_main_#t~nondet0_10_const_-311470069|)
  (|v_main_#t~nondet1_10| |v_main_#t~nondet1_10_const_-311450644|)
  (|v_main_#t~nondet2_10| |v_main_#t~nondet2_10_const_-311546035|))
 (and (>= (+ v_main_~x~2_15 v_main_~y~2_11) 0)
 (not
 (or (>= v_main_~N~2_9 536870912)
 (>= v_main_~x~2_15 536870912)
 (>= v_main_~y~2_11 536870912)
 (< v_main_~x~2_15 (- 1073741824))))
 (= v_main_~x~2_15 |v_main_#t~nondet0_10|)
 (= v_main_~y~2_11 |v_main_#t~nondet1_10|)
 (= v_main_~N~2_9 |v_main_#t~nondet2_10|))))
(assert false)
(assert false)
(assert true)
(assert true)
(assert true)
(declare-const v_main_~x~2_16_const_-1587824586 Int)
(declare-const v_main_~N~2_10_const_1504576018 Int)
(assert
 (let
 ((v_main_~x~2_16 v_main_~x~2_16_const_-1587824586)
  (v_main_~N~2_10 v_main_~N~2_10_const_1504576018))
 (<= v_main_~x~2_16 v_main_~N~2_10)))
(declare-const v_main_~x~2_17_const_-1587824587 Int)
(declare-const v_main_~N~2_11_const_1504576017 Int)
(assert
 (let
 ((v_main_~x~2_17 v_main_~x~2_17_const_-1587824587)
  (v_main_~N~2_11 v_main_~N~2_11_const_1504576017))
 (<= v_main_~x~2_17 v_main_~N~2_11)))
(declare-const v_main_~x~2_18_const_-1587824588 Int)
(declare-const v_main_~x~2_19_const_-1587824589 Int)
(declare-const |v_main_#t~nondet3_6_const_-425615621| Int)
(assert
 (let
 ((v_main_~x~2_18 v_main_~x~2_18_const_-1587824588)
  (v_main_~x~2_19 v_main_~x~2_19_const_-1587824589)
  (|v_main_#t~nondet3_6| |v_main_#t~nondet3_6_const_-425615621|))
 (and (= |v_main_#t~nondet3_6| 0) (= v_main_~x~2_18 (+ v_main_~x~2_19 1)))))
(declare-const v_main_~x~2_20_const_-1587824675 Int)
(declare-const v_main_~x~2_21_const_-1587824676 Int)
(declare-const |v_main_#t~nondet3_8_const_-425615623| Int)
(assert
 (let
 ((v_main_~x~2_20 v_main_~x~2_20_const_-1587824675)
  (v_main_~x~2_21 v_main_~x~2_21_const_-1587824676)
  (|v_main_#t~nondet3_8| |v_main_#t~nondet3_8_const_-425615623|))
 (and (= |v_main_#t~nondet3_8| 0) (= v_main_~x~2_20 (+ v_main_~x~2_21 1)))))
(assert true)
(declare-const v_main_~x~2_23_const_-1587824678 Int)
(declare-const v_main_~y~2_13_const_-1559322790 Int)
(declare-const v_main_~x~2_22_const_-1587824677 Int)
(declare-const |v_main_#t~nondet3_10_const_-311510226| Int)
(declare-const v_main_~y~2_12_const_-1559322789 Int)
(assert
 (let
 ((v_main_~x~2_23 v_main_~x~2_23_const_-1587824678)
  (v_main_~y~2_13 v_main_~y~2_13_const_-1559322790)
  (v_main_~x~2_22 v_main_~x~2_22_const_-1587824677)
  (|v_main_#t~nondet3_10| |v_main_#t~nondet3_10_const_-311510226|)
  (v_main_~y~2_12 v_main_~y~2_12_const_-1559322789))
 (and (not (= |v_main_#t~nondet3_10| 0))
 (= v_main_~x~2_22 (+ (* 2 v_main_~x~2_23) v_main_~y~2_13))
 (= v_main_~y~2_12 (+ v_main_~y~2_13 1)))))
(declare-const v_main_~x~2_25_const_-1587824680 Int)
(declare-const v_main_~y~2_15_const_-1559322792 Int)
(declare-const v_main_~x~2_24_const_-1587824679 Int)
(declare-const |v_main_#t~nondet3_12_const_-311510228| Int)
(declare-const v_main_~y~2_14_const_-1559322791 Int)
(assert
 (let
 ((v_main_~x~2_25 v_main_~x~2_25_const_-1587824680)
  (v_main_~y~2_15 v_main_~y~2_15_const_-1559322792)
  (v_main_~x~2_24 v_main_~x~2_24_const_-1587824679)
  (|v_main_#t~nondet3_12| |v_main_#t~nondet3_12_const_-311510228|)
  (v_main_~y~2_14 v_main_~y~2_14_const_-1559322791))
 (and (not (= |v_main_#t~nondet3_12| 0))
 (= v_main_~x~2_24 (+ (* 2 v_main_~x~2_25) v_main_~y~2_15))
 (= v_main_~y~2_14 (+ v_main_~y~2_15 1)))))
(declare-const v_main_~x~2_26_const_-1587824681 Int)
(declare-const v_main_~N~2_12_const_1504576016 Int)
(assert
 (let
 ((v_main_~x~2_26 v_main_~x~2_26_const_-1587824681)
  (v_main_~N~2_12 v_main_~N~2_12_const_1504576016))
 (not (<= v_main_~x~2_26 v_main_~N~2_12))))
(declare-const v_main_~x~2_27_const_-1587824682 Int)
(declare-const v_main_~N~2_13_const_1504576047 Int)
(assert
 (let
 ((v_main_~x~2_27 v_main_~x~2_27_const_-1587824682)
  (v_main_~N~2_13 v_main_~N~2_13_const_1504576047))
 (not (<= v_main_~x~2_27 v_main_~N~2_13))))
(declare-const v_main_~N~2_14_const_1504576046 Int)
(declare-const v_main_~x~2_28_const_-1587824683 Int)
(declare-const v_main_~y~2_16_const_-1559322793 Int)
(declare-const |v_main_#res_3_const_385270465| Int)
(declare-const |v_main_#t~nondet0_12_const_-311470071| Int)
(declare-const |v_main_#t~nondet1_12_const_-311450646| Int)
(declare-const |v_main_#t~nondet2_12_const_-311546037| Int)
(assert
 (let
 ((v_main_~N~2_14 v_main_~N~2_14_const_1504576046)
  (v_main_~x~2_28 v_main_~x~2_28_const_-1587824683)
  (v_main_~y~2_16 v_main_~y~2_16_const_-1559322793)
  (|v_main_#res_3| |v_main_#res_3_const_385270465|)
  (|v_main_#t~nondet0_12| |v_main_#t~nondet0_12_const_-311470071|)
  (|v_main_#t~nondet1_12| |v_main_#t~nondet1_12_const_-311450646|)
  (|v_main_#t~nondet2_12| |v_main_#t~nondet2_12_const_-311546037|))
 (and
 (or (>= v_main_~N~2_14 536870912)
 (>= v_main_~x~2_28 536870912)
 (>= v_main_~y~2_16 536870912)
 (< v_main_~x~2_28 (- 1073741824)))
 (= |v_main_#res_3| 0) (= v_main_~x~2_28 |v_main_#t~nondet0_12|)
 (= v_main_~y~2_16 |v_main_#t~nondet1_12|)
 (= v_main_~N~2_14 |v_main_#t~nondet2_12|))))
(declare-const v_main_~N~2_15_const_1504576045 Int)
(declare-const v_main_~x~2_29_const_-1587824684 Int)
(declare-const v_main_~y~2_17_const_-1559322794 Int)
(declare-const |v_main_#res_4_const_385270464| Int)
(declare-const |v_main_#t~nondet0_14_const_-311470073| Int)
(declare-const |v_main_#t~nondet1_14_const_-311450648| Int)
(declare-const |v_main_#t~nondet2_14_const_-311546039| Int)
(assert
 (let
 ((v_main_~N~2_15 v_main_~N~2_15_const_1504576045)
  (v_main_~x~2_29 v_main_~x~2_29_const_-1587824684)
  (v_main_~y~2_17 v_main_~y~2_17_const_-1559322794)
  (|v_main_#res_4| |v_main_#res_4_const_385270464|)
  (|v_main_#t~nondet0_14| |v_main_#t~nondet0_14_const_-311470073|)
  (|v_main_#t~nondet1_14| |v_main_#t~nondet1_14_const_-311450648|)
  (|v_main_#t~nondet2_14| |v_main_#t~nondet2_14_const_-311546039|))
 (and
 (or (>= v_main_~N~2_15 536870912)
 (>= v_main_~x~2_29 536870912)
 (>= v_main_~y~2_17 536870912)
 (< v_main_~x~2_29 (- 1073741824)))
 (= |v_main_#res_4| 0) (= v_main_~x~2_29 |v_main_#t~nondet0_14|)
 (= v_main_~y~2_17 |v_main_#t~nondet1_14|)
 (= v_main_~N~2_15 |v_main_#t~nondet2_14|))))
(declare-const c_unseeded Bool)
(declare-const c_oldRank0 Int)
(declare-const c_oldRank1 Int)
(declare-const |main_#t~nondet0_1| Int)
(declare-const |main_#t~nondet2_1| Int)
(declare-const |main_#t~nondet1_1| Int)
(declare-const main_~y~2_2 Int)
(declare-const main_~N~2_2 Int)
(declare-const main_~x~2_2 Int)
(assert true)
(assert (not false))
(assert true)
(assert true)
(assert true)
(assert true)
(assert
 (and (>= (+ main_~x~2_2 main_~y~2_2) 0)
 (not
 (or (>= main_~N~2_2 536870912)
 (>= main_~x~2_2 536870912)
 (>= main_~y~2_2 536870912)
 (< main_~x~2_2 (- 1073741824))))
 (= main_~x~2_2 |main_#t~nondet0_1|)
 (= main_~y~2_2 |main_#t~nondet1_1|)
 (= main_~N~2_2 |main_#t~nondet2_1|)))
(declare-const main_~N~2_-1 Int)
(declare-const main_~x~2_-1 Int)
(declare-const main_~y~2_-1 Int)
(declare-const |main_#t~nondet3_-1| Int)
(declare-const main_~y~2_2 Int)
(declare-const main_~x~2_2 Int)
(assert true)
(assert (not false))
(assert true)
(assert (<= main_~x~2_-1 main_~N~2_-1))
(assert
 (and (not (= |main_#t~nondet3_-1| 0))
 (= main_~x~2_2 (+ (* 2 main_~x~2_-1) main_~y~2_-1))
 (= main_~y~2_2 (+ main_~y~2_-1 1))))
(assert true)
(declare-const |main_#t~nondet0_1| Int)
(declare-const |main_#t~nondet2_1| Int)
(declare-const |main_#t~nondet1_1| Int)
(declare-const main_~y~2_2 Int)
(declare-const main_~N~2_2 Int)
(declare-const main_~x~2_2 Int)
(declare-const |main_#t~nondet3_1| Int)
(declare-const main_~y~2_5 Int)
(declare-const main_~x~2_5 Int)
(assert true)
(assert (not false))
(assert true)
(assert true)
(assert true)
(assert true)
(assert
 (and (>= (+ main_~x~2_2 main_~y~2_2) 0)
 (not
 (or (>= main_~N~2_2 536870912)
 (>= main_~x~2_2 536870912)
 (>= main_~y~2_2 536870912)
 (< main_~x~2_2 (- 1073741824))))
 (= main_~x~2_2 |main_#t~nondet0_1|)
 (= main_~y~2_2 |main_#t~nondet1_1|)
 (= main_~N~2_2 |main_#t~nondet2_1|)))
(assert true)
(assert (<= main_~x~2_2 main_~N~2_2))
(assert
 (and (not (= |main_#t~nondet3_1| 0))
 (= main_~x~2_5 (+ (* 2 main_~x~2_2) main_~y~2_2))
 (= main_~y~2_5 (+ main_~y~2_2 1))))
(assert true)
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(assert
 (not
 (and (not (= |v_main_#t~nondet3_14_const_-311510230| 0))
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796))
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and (not (= |v_main_#t~nondet3_14_const_-311510230| 0))
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796))
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796))))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(assert
 (not
 (and (not (= |v_main_#t~nondet3_14_const_-311510230| 0))
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796))
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and (not (= |v_main_#t~nondet3_14_const_-311510230| 0))
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796))
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796))))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (not (= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (= v_main_~x~2_30_const_-1587824642
 (+ (* 2 v_main_~x~2_31_const_-1587824643) v_main_~y~2_19_const_-1559322796)))
(assert
 (= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert false)
(assert false)
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(assert
 (not
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))))
(assert
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(assert
 (not
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))))
(assert
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert false)
(assert false)
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))))
(assert
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))))
(assert
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(declare-const v_main_~N~2_17_const_1504576043 Int)
(declare-const v_main_~x~2_32_const_-1587824644 Int)
(declare-const v_main_~y~2_20_const_-1559322754 Int)
(declare-const |v_main_#t~nondet0_16_const_-311470075| Int)
(declare-const |v_main_#t~nondet1_16_const_-311450650| Int)
(declare-const |v_main_#t~nondet2_16_const_-311546041| Int)
(assert
 (not
 (and
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)
 (< v_main_~x~2_32_const_-1587824644 (- 1073741824))))
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))))
(assert
 (and
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)
 (< v_main_~x~2_32_const_-1587824644 (- 1073741824))))
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|)))
(assert
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)
 (< v_main_~x~2_32_const_-1587824644 (- 1073741824)))))
(assert
 (not
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)
 (< v_main_~x~2_32_const_-1587824644 (- 1073741824)))))
(assert
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)
 (< v_main_~x~2_32_const_-1587824644 (- 1073741824))))
(assert (not (< v_main_~x~2_32_const_-1587824644 (- 1073741824))))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (>= v_main_~N~2_17_const_1504576043 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (>= v_main_~x~2_32_const_-1587824644 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (>= v_main_~y~2_20_const_-1559322754 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (not (< v_main_~x~2_32_const_-1587824644 (- 1073741824))))
(assert (< v_main_~x~2_32_const_-1587824644 (- 1073741824)))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (not
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (not
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (not
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|)))
(assert
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))
(assert
 (not
 (and
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)))
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))))
(assert
 (and
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)))
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|)))
(assert
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (not
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (>= v_main_~N~2_17_const_1504576043 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (>= v_main_~x~2_32_const_-1587824644 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (>= v_main_~y~2_20_const_-1559322754 536870912))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (not
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (not
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (not
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|)))
(assert
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))
(declare-const v_main_~N~2_17_const_1504576043 Int)
(declare-const v_main_~x~2_32_const_-1587824644 Int)
(declare-const v_main_~y~2_20_const_-1559322754 Int)
(declare-const |v_main_#t~nondet0_16_const_-311470075| Int)
(declare-const |v_main_#t~nondet1_16_const_-311450650| Int)
(declare-const |v_main_#t~nondet2_16_const_-311546041| Int)
(assert
 (not
 (and
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)))
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))))
(assert
 (and
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)))
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|)))
(assert
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (not
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0)))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (>= v_main_~N~2_17_const_1504576043 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (>= v_main_~x~2_32_const_-1587824644 536870912))
(assert (not (>= v_main_~N~2_17_const_1504576043 536870912)))
(assert (not (>= v_main_~x~2_32_const_-1587824644 536870912)))
(assert (not (>= v_main_~y~2_20_const_-1559322754 536870912)))
(assert (>= v_main_~y~2_20_const_-1559322754 536870912))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (not
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|)))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (not
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|)))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (>= (+ v_main_~x~2_32_const_-1587824644 v_main_~y~2_20_const_-1559322754) 0))
(assert
 (not
 (or (>= v_main_~N~2_17_const_1504576043 536870912)
 (>= v_main_~x~2_32_const_-1587824644 536870912)
 (>= v_main_~y~2_20_const_-1559322754 536870912))))
(assert
 (= v_main_~x~2_32_const_-1587824644 |v_main_#t~nondet0_16_const_-311470075|))
(assert
 (= v_main_~y~2_20_const_-1559322754 |v_main_#t~nondet1_16_const_-311450650|))
(assert
 (not
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|)))
(assert
 (= v_main_~N~2_17_const_1504576043 |v_main_#t~nondet2_16_const_-311546041|))
(assert false)
(assert false)
(declare-const v_main_~N~2_18_const_1504576042 Int)
(declare-const v_main_~x~2_33_const_-1587824645 Int)
(declare-const v_main_~y~2_21_const_-1559322755 Int)
(declare-const |v_main_#t~nondet0_18_const_-311470077| Int)
(declare-const |v_main_#t~nondet1_18_const_-311450652| Int)
(declare-const |v_main_#t~nondet2_18_const_-311546043| Int)
(assert
 (not
 (and
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0)
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912)))
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|)
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|)
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|))))
(assert
 (and
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0)
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912)))
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|)
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|)
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|)))
(assert
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|))
(assert
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (not
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0)))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912)))
(assert (not (>= v_main_~y~2_21_const_-1559322755 536870912)))
(assert (not (>= v_main_~x~2_33_const_-1587824645 536870912)))
(assert (not (>= v_main_~N~2_18_const_1504576042 536870912)))
(assert (>= v_main_~N~2_18_const_1504576042 536870912))
(assert (not (>= v_main_~N~2_18_const_1504576042 536870912)))
(assert (not (>= v_main_~x~2_33_const_-1587824645 536870912)))
(assert (>= v_main_~x~2_33_const_-1587824645 536870912))
(assert (not (>= v_main_~N~2_18_const_1504576042 536870912)))
(assert (not (>= v_main_~x~2_33_const_-1587824645 536870912)))
(assert (not (>= v_main_~y~2_21_const_-1559322755 536870912)))
(assert (>= v_main_~y~2_21_const_-1559322755 536870912))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (not
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|)))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (not
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|)))
(assert
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|))
(assert
 (not
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|)))
(assert
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|))
(declare-const v_main_~N~2_18_const_1504576042 Int)
(declare-const v_main_~x~2_33_const_-1587824645 Int)
(declare-const v_main_~y~2_21_const_-1559322755 Int)
(declare-const |v_main_#t~nondet0_18_const_-311470077| Int)
(declare-const |v_main_#t~nondet1_18_const_-311450652| Int)
(declare-const |v_main_#t~nondet2_18_const_-311546043| Int)
(assert
 (not
 (and
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0)
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912)))
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|)
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|)
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|))))
(assert
 (and
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0)
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912)))
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|)
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|)
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|)))
(assert
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|))
(assert
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (not
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0)))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912)))
(assert (not (>= v_main_~y~2_21_const_-1559322755 536870912)))
(assert (not (>= v_main_~x~2_33_const_-1587824645 536870912)))
(assert (not (>= v_main_~N~2_18_const_1504576042 536870912)))
(assert (>= v_main_~N~2_18_const_1504576042 536870912))
(assert (not (>= v_main_~N~2_18_const_1504576042 536870912)))
(assert (not (>= v_main_~x~2_33_const_-1587824645 536870912)))
(assert (>= v_main_~x~2_33_const_-1587824645 536870912))
(assert (not (>= v_main_~N~2_18_const_1504576042 536870912)))
(assert (not (>= v_main_~x~2_33_const_-1587824645 536870912)))
(assert (not (>= v_main_~y~2_21_const_-1559322755 536870912)))
(assert (>= v_main_~y~2_21_const_-1559322755 536870912))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (not
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|)))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (not
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|)))
(assert
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|))
(assert
 (>= (+ v_main_~x~2_33_const_-1587824645 v_main_~y~2_21_const_-1559322755) 0))
(assert
 (not
 (or (>= v_main_~N~2_18_const_1504576042 536870912)
 (>= v_main_~x~2_33_const_-1587824645 536870912)
 (>= v_main_~y~2_21_const_-1559322755 536870912))))
(assert
 (= v_main_~x~2_33_const_-1587824645 |v_main_#t~nondet0_18_const_-311470077|))
(assert
 (= v_main_~y~2_21_const_-1559322755 |v_main_#t~nondet1_18_const_-311450652|))
(assert
 (not
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|)))
(assert
 (= v_main_~N~2_18_const_1504576042 |v_main_#t~nondet2_18_const_-311546043|))
(declare-const v_main_~N~2_19_const_1504576041 Int)
(declare-const v_main_~x~2_34_const_-1587824646 Int)
(declare-const v_main_~y~2_22_const_-1559322756 Int)
(declare-const |v_main_#t~nondet0_20_const_-311470036| Int)
(declare-const |v_main_#t~nondet1_20_const_-311450739| Int)
(declare-const |v_main_#t~nondet2_20_const_-311546002| Int)
(assert
 (not
 (and
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912)))
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|)
 (= v_main_~y~2_22_const_-1559322756 |v_main_#t~nondet1_20_const_-311450739|)
 (= v_main_~N~2_19_const_1504576041 |v_main_#t~nondet2_20_const_-311546002|))))
(assert
 (and
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912)))
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|)
 (= v_main_~y~2_22_const_-1559322756 |v_main_#t~nondet1_20_const_-311450739|)
 (= v_main_~N~2_19_const_1504576041 |v_main_#t~nondet2_20_const_-311546002|)))
(assert
 (= v_main_~N~2_19_const_1504576041 |v_main_#t~nondet2_20_const_-311546002|))
(assert
 (= v_main_~y~2_22_const_-1559322756 |v_main_#t~nondet1_20_const_-311450739|))
(assert
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|))
(assert
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912))))
(assert
 (not
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912))))
(assert
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (>= v_main_~N~2_19_const_1504576041 536870912))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (>= v_main_~x~2_34_const_-1587824646 536870912))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (>= v_main_~y~2_22_const_-1559322756 536870912))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912))))
(assert
 (not
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|)))
(assert
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912))))
(assert
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|))
(assert
 (not
 (= v_main_~y~2_22_const_-1559322756 |v_main_#t~nondet1_20_const_-311450739|)))
(assert
 (= v_main_~y~2_22_const_-1559322756 |v_main_#t~nondet1_20_const_-311450739|))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert
 (not
 (or (>= v_main_~N~2_19_const_1504576041 536870912)
 (>= v_main_~x~2_34_const_-1587824646 536870912)
 (>= v_main_~y~2_22_const_-1559322756 536870912))))
(assert
 (= v_main_~x~2_34_const_-1587824646 |v_main_#t~nondet0_20_const_-311470036|))
(assert
 (= v_main_~y~2_22_const_-1559322756 |v_main_#t~nondet1_20_const_-311450739|))
(assert
 (not
 (= v_main_~N~2_19_const_1504576041 |v_main_#t~nondet2_20_const_-311546002|)))
(assert
 (= v_main_~N~2_19_const_1504576041 |v_main_#t~nondet2_20_const_-311546002|))
(declare-const v_main_~x~2_34_const_-1587824646 Int)
(declare-const v_main_~y~2_22_const_-1559322756 Int)
(declare-const v_main_~N~2_19_const_1504576041 Int)
(assert
 (not
 (and
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912))
 (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (not (>= v_main_~N~2_19_const_1504576041 536870912)))))
(assert
 (and
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912))
 (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (not (>= v_main_~N~2_19_const_1504576041 536870912))))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert
 (not
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (>= v_main_~x~2_34_const_-1587824646 536870912))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (>= v_main_~y~2_22_const_-1559322756 536870912))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (>= v_main_~N~2_19_const_1504576041 536870912))
(declare-const v_main_~x~2_34_const_-1587824646 Int)
(declare-const v_main_~y~2_22_const_-1559322756 Int)
(declare-const v_main_~N~2_19_const_1504576041 Int)
(assert
 (not
 (and (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912)))))
(assert
 (and (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912))))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (>= v_main_~N~2_19_const_1504576041 536870912))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (>= v_main_~y~2_22_const_-1559322756 536870912))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert
 (not
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (>= v_main_~x~2_34_const_-1587824646 536870912))
(declare-const v_main_~x~2_34_const_-1587824646 Int)
(declare-const v_main_~y~2_22_const_-1559322756 Int)
(declare-const v_main_~N~2_19_const_1504576041 Int)
(assert
 (not
 (and (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912)))))
(assert
 (and (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912))))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (>= v_main_~N~2_19_const_1504576041 536870912))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (>= v_main_~y~2_22_const_-1559322756 536870912))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert
 (not
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (>= v_main_~x~2_34_const_-1587824646 536870912))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(assert
 (not
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))))
(assert
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(assert
 (not
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))))
(assert
 (and
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (and (<= |v_main_#t~nondet3_14_const_-311510230| 0)
 (>= |v_main_#t~nondet3_14_const_-311510230| 0))))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(declare-const v_main_~x~2_34_const_-1587824646 Int)
(declare-const v_main_~y~2_22_const_-1559322756 Int)
(declare-const v_main_~N~2_19_const_1504576041 Int)
(assert
 (not
 (and (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912)))))
(assert
 (and (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912))))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (>= v_main_~y~2_22_const_-1559322756 536870912))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (>= v_main_~N~2_19_const_1504576041 536870912))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert
 (not
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (>= v_main_~x~2_34_const_-1587824646 536870912))
(declare-const v_main_~x~2_34_const_-1587824646 Int)
(declare-const v_main_~y~2_22_const_-1559322756 Int)
(declare-const v_main_~N~2_19_const_1504576041 Int)
(assert
 (not
 (and (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912)))))
(assert
 (and (not (>= v_main_~y~2_22_const_-1559322756 536870912))
 (not (>= v_main_~N~2_19_const_1504576041 536870912))
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)
 (not (>= v_main_~x~2_34_const_-1587824646 536870912))))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (>= v_main_~y~2_22_const_-1559322756 536870912))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert (>= v_main_~N~2_19_const_1504576041 536870912))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert
 (not
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~y~2_22_const_-1559322756 536870912)))
(assert (not (>= v_main_~N~2_19_const_1504576041 536870912)))
(assert
 (>= (+ v_main_~x~2_34_const_-1587824646 v_main_~y~2_22_const_-1559322756) 0))
(assert (not (>= v_main_~x~2_34_const_-1587824646 536870912)))
(assert (>= v_main_~x~2_34_const_-1587824646 536870912))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))))
(assert
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(declare-const v_main_~x~2_31_const_-1587824643 Int)
(declare-const v_main_~y~2_19_const_-1559322796 Int)
(declare-const v_main_~x~2_30_const_-1587824642 Int)
(declare-const v_main_~y~2_18_const_-1559322795 Int)
(declare-const |v_main_#t~nondet3_14_const_-311510230| Int)
(declare-const v_main_~N~2_16_const_1504576044 Int)
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))))
(assert
 (or
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (>= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (>= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (>= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (not
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))))
(assert
 (and
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (not (<= |v_main_#t~nondet3_14_const_-311510230| 0))
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))
 (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert (<= |v_main_#t~nondet3_14_const_-311510230| 0))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (not
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796))))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (not
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1))))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (>= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (<= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert (not (<= |v_main_#t~nondet3_14_const_-311510230| 0)))
(assert
 (>= v_main_~x~2_30_const_-1587824642
 (+ (* v_main_~x~2_31_const_-1587824643 2) v_main_~y~2_19_const_-1559322796)))
(assert
 (<= v_main_~y~2_18_const_-1559322795 (+ v_main_~y~2_19_const_-1559322796 1)))
(assert
 (not (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044)))
(assert (<= v_main_~x~2_31_const_-1587824643 v_main_~N~2_16_const_1504576044))
(declare-const main_~N~2_0 Int)
(declare-const main_~y~2_0 Int)
(declare-const oldRank1_0 Int)
(declare-const oldRank0_0 Int)
(declare-const main_~x~2_0 Int)
(declare-const |main_#t~nondet3_0| Int)
(declare-const main_~y~2_1 Int)
(declare-const |main_#t~nondet3_1| Int)
(declare-const main_~x~2_1 Int)
(assert
 (and
 (let
 ((main_~x~2 main_~x~2_0)
  (main_~N~2 main_~N~2_0)
  (oldRank1 oldRank1_0)
  (oldRank0 oldRank0_0)
  (main_~y~2 main_~y~2_0))
 (and
 (>= oldRank0
 (ite (> (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32) 0) 1 0))
 (>= oldRank1
 (ite (> (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32) 0)
 (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32)
 (+ main_~N~2 (* (- 1) main_~x~2) 32)))))
 (let ((v_main_~x~2_30 main_~x~2_1))
 (let ((v_main_~y~2_18 main_~y~2_1))
 (let ((v_main_~x~2_31 main_~x~2_0))
 (let ((|v_main_#t~nondet3_14| |main_#t~nondet3_0|))
 (let ((v_main_~y~2_19 main_~y~2_0))
 (let ((v_main_~N~2_16 main_~N~2_0))
 (and (not (= |v_main_#t~nondet3_14| 0))
 (= v_main_~x~2_30 (+ (* 2 v_main_~x~2_31) v_main_~y~2_19))
 (= v_main_~y~2_18 (+ v_main_~y~2_19 1))
 (<= v_main_~x~2_31 v_main_~N~2_16))))))))
 (not
 (let
 ((main_~x~2 main_~x~2_1)
  (main_~N~2 main_~N~2_0)
  (oldRank1 oldRank1_0)
  (oldRank0 oldRank0_0)
  (main_~y~2 main_~y~2_1))
 (or
 (and
 (> oldRank0
 (ite (> (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32) 0) 1 0))
 (>= oldRank0 0))
 (and
 (>= oldRank0
 (ite (> (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32) 0) 1 0))
 (> oldRank1
 (ite (> (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32) 0)
 (+ (* (- 1) main_~y~2) main_~N~2 (* (- 2) main_~x~2) 32)
 (+ main_~N~2 (* (- 1) main_~x~2) 32)))
 (>= oldRank1 0)))))))
(assert c_unseeded)
(assert (not false))
(assert true)
(assert (not c_unseeded))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert (not false))
(assert true)
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert (not c_unseeded))
(assert c_unseeded)
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert (not false))
(assert true)
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert (not c_unseeded))
(assert c_unseeded)
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert (not false))
(assert true)
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert (not c_unseeded))
(assert c_unseeded)
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(declare-const unseeded_-1 Bool)
(declare-const oldRank7_-1 Int)
(declare-const oldRank1_-1 Int)
(declare-const oldRank9_-1 Int)
(declare-const oldRank6_-1 Int)
(declare-const oldRank4_-1 Int)
(declare-const oldRank3_-1 Int)
(declare-const oldRank2_-1 Int)
(declare-const oldRank5_-1 Int)
(declare-const oldRank0_-1 Int)
(declare-const oldRank8_-1 Int)
(declare-const |old(oldRank9)_1| Int)
(declare-const |old(oldRank4)_1| Int)
(declare-const |old(oldRank7)_1| Int)
(declare-const |old(oldRank0)_1| Int)
(declare-const |old(unseeded)_1| Bool)
(declare-const |old(oldRank1)_1| Int)
(declare-const |old(oldRank5)_1| Int)
(declare-const |old(oldRank2)_1| Int)
(declare-const |old(oldRank6)_1| Int)
(declare-const |old(oldRank8)_1| Int)
(declare-const |old(oldRank3)_1| Int)
(declare-const unseeded_1 Bool)
(declare-const oldRank7_1 Int)
(declare-const oldRank1_1 Int)
(declare-const oldRank9_1 Int)
(declare-const oldRank6_1 Int)
(declare-const oldRank4_1 Int)
(declare-const oldRank3_1 Int)
(declare-const oldRank2_1 Int)
(declare-const oldRank5_1 Int)
(declare-const oldRank0_1 Int)
(declare-const oldRank8_1 Int)
(declare-const |main_#t~nondet0_1| Int)
(declare-const |main_#t~nondet2_1| Int)
(declare-const |main_#t~nondet1_1| Int)
(declare-const main_~y~2_2 Int)
(declare-const main_~N~2_2 Int)
(declare-const main_~x~2_2 Int)
(assert unseeded_-1)
(assert (not (and unseeded_1 (>= (+ main_~y~2_2 main_~x~2_2 0) 0))))
(assert true)
(assert
 (and (= unseeded_1 |old(unseeded)_1|)
 (= oldRank0_1 |old(oldRank0)_1|)
 (= oldRank1_1 |old(oldRank1)_1|)
 (= oldRank2_1 |old(oldRank2)_1|)
 (= oldRank3_1 |old(oldRank3)_1|)
 (= oldRank4_1 |old(oldRank4)_1|)
 (= oldRank5_1 |old(oldRank5)_1|)
 (= oldRank6_1 |old(oldRank6)_1|)
 (= oldRank7_1 |old(oldRank7)_1|)
 (= oldRank8_1 |old(oldRank8)_1|)
 (= oldRank9_1 |old(oldRank9)_1|)))
(assert true)
(assert
 (and (= unseeded_-1 |old(unseeded)_1|)
 (= oldRank0_-1 |old(oldRank0)_1|)
 (= oldRank1_-1 |old(oldRank1)_1|)
 (= oldRank2_-1 |old(oldRank2)_1|)
 (= oldRank3_-1 |old(oldRank3)_1|)
 (= oldRank4_-1 |old(oldRank4)_1|)
 (= oldRank5_-1 |old(oldRank5)_1|)
 (= oldRank6_-1 |old(oldRank6)_1|)
 (= oldRank7_-1 |old(oldRank7)_1|)
 (= oldRank8_-1 |old(oldRank8)_1|)
 (= oldRank9_-1 |old(oldRank9)_1|)))
(assert
 (and (>= (+ main_~x~2_2 main_~y~2_2) 0)
 (not
 (or (>= main_~N~2_2 536870912)
 (>= main_~x~2_2 536870912)
 (>= main_~y~2_2 536870912)
 (< main_~x~2_2 (- 1073741824))))
 (= main_~x~2_2 |main_#t~nondet0_1|)
 (= main_~y~2_2 |main_#t~nondet1_1|)
 (= main_~N~2_2 |main_#t~nondet2_1|)))
(declare-const unseeded_-1 Bool)
(declare-const oldRank7_-1 Int)
(declare-const oldRank1_-1 Int)
(declare-const oldRank9_-1 Int)
(declare-const oldRank6_-1 Int)
(declare-const oldRank4_-1 Int)
(declare-const oldRank3_-1 Int)
(declare-const oldRank2_-1 Int)
(declare-const oldRank5_-1 Int)
(declare-const oldRank0_-1 Int)
(declare-const oldRank8_-1 Int)
(declare-const main_~y~2_-1 Int)
(declare-const main_~N~2_-1 Int)
(declare-const main_~x~2_-1 Int)
(declare-const |main_#t~nondet3_-1| Int)
(declare-const main_~y~2_2 Int)
(declare-const main_~x~2_2 Int)
(assert
 (and
 (>= oldRank0_-1
 (ite (> (+ (* (- 1) main_~y~2_-1) main_~N~2_-1 (* (- 2) main_~x~2_-1) 32) 0)
 1 0))
 (>= oldRank1_-1
 (ite (> (+ (* (- 1) main_~y~2_-1) main_~N~2_-1 (* (- 2) main_~x~2_-1) 32) 0)
 (+ (* (- 1) main_~y~2_-1) main_~N~2_-1 (* (- 2) main_~x~2_-1) 32)
 (+ main_~N~2_-1 (* (- 1) main_~x~2_-1) 32)))
 (>= (+ main_~y~2_-1 main_~x~2_-1 0) 0)))
(assert
 (not
 (and (>= (+ main_~y~2_2 main_~x~2_2 0) 0)
 (or unseeded_-1
 (and
 (> oldRank0_-1
 (ite (> (+ (* (- 1) main_~y~2_2) main_~N~2_-1 (* (- 2) main_~x~2_2) 32) 0) 1
 0)) (>= oldRank0_-1 0))
 (and
 (>= oldRank0_-1
 (ite (> (+ (* (- 1) main_~y~2_2) main_~N~2_-1 (* (- 2) main_~x~2_2) 32) 0) 1
 0))
 (> oldRank1_-1
 (ite (> (+ (* (- 1) main_~y~2_2) main_~N~2_-1 (* (- 2) main_~x~2_2) 32) 0)
 (+ (* (- 1) main_~y~2_2) main_~N~2_-1 (* (- 2) main_~x~2_2) 32)
 (+ main_~N~2_-1 (* (- 1) main_~x~2_2) 32)))
 (>= oldRank1_-1 0))))))
(assert true)
(assert (<= main_~x~2_-1 main_~N~2_-1))
(assert
 (and (not (= |main_#t~nondet3_-1| 0))
 (= main_~x~2_2 (+ (* 2 main_~x~2_-1) main_~y~2_-1))
 (= main_~y~2_2 (+ main_~y~2_-1 1))))
(assert true)
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32))))))
(assert (not false))
(assert true)
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32))))))
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32))))))
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32))))))
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32))))))
(assert (not c_unseeded))
(assert c_unseeded)
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 32)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (* 2 c_main_~N~2) (+ (* 3 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 32)))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))
 (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 32)))))))
(declare-const main_~x~2_const_-250648389 Int)
(declare-const main_~y~2_const_-250649350 Int)
(declare-const oldRank1_const_186139729 Int)
(declare-const main_~N~2_const_-250821115 Int)
(declare-const oldRank0_const_186139730 Int)
(assert
 (not
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))))
(assert
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (not (<= 0 (+ oldRank0_const_186139730 (- 1)))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32)))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))))
(assert
 (not
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))
(assert
 (not
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350) 0)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))))
(assert true)
(assert
 (not
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= (* 2 main_~N~2_const_-250821115)
 (+ (* 3 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64)))))
(assert true)
(assert (not (<= 0 oldRank0_const_186139730)))
(assert (<= 0 oldRank0_const_186139730))
(assert true)
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
(assert true)
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
(assert
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))
(assert
 (not
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
 (and
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
 (and
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))))
(assert
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (not (<= 0 (+ oldRank0_const_186139730 (- 1)))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 32))))))
(assert
 (not
 (and
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))
(assert
 (not
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))))
(assert
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
(assert (not (<= 0 oldRank0_const_186139730)))
(assert (<= 0 oldRank0_const_186139730))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32))))
(assert
 (and (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 32)))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 32))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert (not false))
(assert true)
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert (not c_unseeded))
(assert c_unseeded)
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2
 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (* 3 c_oldRank1) (- 96)))
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32))))
 (and
 (or
 (and
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) c_oldRank1 (- 32)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0)
 (<= c_main_~N~2 (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2) (- 96)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 32)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(declare-const main_~x~2_const_-250648389 Int)
(declare-const main_~y~2_const_-250649350 Int)
(declare-const oldRank1_const_186139729 Int)
(declare-const main_~N~2_const_-250821115 Int)
(declare-const oldRank0_const_186139730 Int)
(assert
 (not
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))))
(assert
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (not (<= 0 (+ oldRank0_const_186139730 (- 1)))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))))
(assert
 (not
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (not
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350))
 main_~N~2_const_-250821115)
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))))
(assert true)
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (not (<= 0 oldRank0_const_186139730)))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert
 (not
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
(assert (not (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))))
(assert (not (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (not
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))))
(assert
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (not (<= 0 (+ oldRank0_const_186139730 (- 1)))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96))))
(assert (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350)))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350)
 (* 3 oldRank1_const_186139729)
 (- 96)))
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389)
 (* 3 main_~y~2_const_-250649350) oldRank1_const_186139729
 (- 32))))))
(assert
 (not
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (not (<= 0 oldRank0_const_186139730)))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96))))
(assert
 (not
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 64))) (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 4 main_~x~2_const_-250648389) (* 3 main_~y~2_const_-250649350) (- 96)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 32)))))
(assert (not (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert (not false))
(assert true)
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert (not (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert (and c_unseeded (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0))))))
(assert
 (and (>= (+ c_main_~y~2 c_main_~x~2 0) 0)
 (or c_unseeded
 (and
 (> c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0)) (>= c_oldRank0 0))
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (> c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= c_oldRank1 0)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ c_main_~x~2 c_main_~y~2) 0)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and
 (<= (+ (* 2 c_main_~N~2) 64) (+ (* 3 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0) (<= (+ c_main_~N~2 32) (+ (* 2 c_main_~x~2) c_main_~y~2))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1))))
 (<= (+ c_main_~N~2 32) (+ c_main_~x~2 c_oldRank1)))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 96)
 (+ (* 4 c_main_~x~2) (* 3 c_oldRank1) (* 3 c_main_~y~2)))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= (+ c_main_~N~2 64) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0)
 (<= (+ c_main_~N~2 96) (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)))
 (<= 32 (+ c_main_~x~2 c_main_~y~2))
 (<= 32 c_oldRank1))) (<= 32 c_oldRank1)))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 96)
 (+ (* 4 c_main_~x~2) (* 3 c_oldRank1) (* 3 c_main_~y~2)))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= (+ c_main_~N~2 64) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0)
 (<= (+ c_main_~N~2 96) (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)))
 (<= 32 (+ c_main_~x~2 c_main_~y~2))
 (<= 32 c_oldRank1))) (<= 32 c_oldRank1))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 96)
 (+ (* 4 c_main_~x~2) (* 3 c_oldRank1) (* 3 c_main_~y~2)))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= (+ c_main_~N~2 64) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0)
 (<= (+ c_main_~N~2 96) (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)))
 (<= 32 (+ c_main_~x~2 c_main_~y~2))
 (<= 32 c_oldRank1))) (<= 32 c_oldRank1)))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2))
 (<= 1 c_oldRank0)
 (<= (+ c_main_~N~2 96)
 (+ (* 4 c_main_~x~2) (* 3 c_oldRank1) (* 3 c_main_~y~2)))
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2))))
 (and
 (or
 (and
 (<= (+ c_main_~N~2 32) (+ (* 4 c_main_~x~2) c_oldRank1 (* 3 c_main_~y~2)))
 (<= 1 c_oldRank0) (<= (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)) c_main_~N~2)
 (<= 0 (+ c_main_~x~2 c_main_~y~2)))
 (and (<= (+ c_main_~N~2 64) (+ (* 2 c_main_~x~2) c_oldRank1 c_main_~y~2))
 (<= 0 c_oldRank0)
 (<= (+ c_main_~N~2 96) (+ (* 4 c_main_~x~2) (* 3 c_main_~y~2)))
 (<= 32 (+ c_main_~x~2 c_main_~y~2))
 (<= 32 c_oldRank1))) (<= 32 c_oldRank1))))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert
 (not
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0))))
(assert
 (and
 (>= c_oldRank0
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0) 1
 0))
 (>= c_oldRank1
 (ite (> (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32) 0)
 (+ (* (- 1) c_main_~y~2) c_main_~N~2 (* (- 2) c_main_~x~2) 32)
 (+ c_main_~N~2 (* (- 1) c_main_~x~2) 32)))
 (>= (+ c_main_~y~2 c_main_~x~2 0) 0)))
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32))))))
(assert (not c_unseeded))
(assert c_unseeded)
(assert
 (not
 (or
 (and (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (* 3 c_oldRank1) (- 97)))
 (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33))))
 (and
 (or
 (and (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 c_oldRank1 (- 33)))
 (<= 0 (+ c_oldRank0 (- 1)))
 (<= (+ (* 2 c_main_~x~2) c_main_~y~2) (+ c_main_~N~2 1))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 1))))
 (and (<= c_main_~N~2 (+ c_main_~x~2 c_oldRank1 (- 64)))
 (<= 0 c_oldRank0) (<= c_main_~N~2 (+ (* 2 c_main_~x~2) c_main_~y~2 (- 97)))
 (<= 0 (+ c_main_~x~2 c_main_~y~2 (- 65)))
 (<= 0 (+ c_oldRank1 (- 32)))))
 (<= 0 (+ c_oldRank1 (- 32)))))))
(declare-const main_~x~2_const_-250648389 Int)
(declare-const main_~y~2_const_-250649350 Int)
(declare-const oldRank1_const_186139729 Int)
(declare-const main_~N~2_const_-250821115 Int)
(declare-const oldRank0_const_186139730 Int)
(assert
 (not
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))))
(assert
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert (not (<= 0 (+ oldRank0_const_186139730 (- 1)))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))))
(assert
 (not
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (not
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))) (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350)
 (+ main_~N~2_const_-250821115 1))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))))
(assert true)
(assert
 (not
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64))))
(assert (not (<= 0 oldRank0_const_186139730)))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97))))
(assert
 (not
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
(assert
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64))))
(assert (<= 0 oldRank0_const_186139730))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
(assert (not (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65)))))
(assert (not (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
(assert
 (not
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))))
(assert
 (or
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))))
(assert
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert (not (<= 0 (+ oldRank0_const_186139730 (- 1)))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97))))
(assert
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1))))
(assert (<= 0 (+ oldRank0_const_186139730 (- 1))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97))))
(assert
 (not
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33)))))
(assert
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))
(assert
 (not
 (and (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 1)))
 (<= 0 (+ oldRank0_const_186139730 (- 1)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 (* 3 oldRank1_const_186139729)
 (- 97)))
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350
 oldRank1_const_186139729
 (- 33))))))
(assert
 (not
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
 (<= 0 (+ oldRank1_const_186139729 (- 32))))))
(assert
 (and
 (and
 (<= main_~N~2_const_-250821115
 (+ main_~x~2_const_-250648389 oldRank1_const_186139729 (- 64)))
 (<= 0 oldRank0_const_186139730)
 (<= main_~N~2_const_-250821115
 (+ (* 2 main_~x~2_const_-250648389) main_~y~2_const_-250649350 (- 97)))
 (<= 0 (+ main_~x~2_const_-250648389 main_~y~2_const_-250649350 (- 65))))
 (<= 0 (+ oldRank1_const_186139729 (- 32)))))
(assert (<= 0 (+ oldRank1_const_186139729 (- 32))))
