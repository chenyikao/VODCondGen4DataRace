

(declare-sort Char)
(define-sort Str () (Array Int Char))
(echo "Simulating signed 128 bit number domain...")
(echo "(including GNU C int128 (2's complement) and IEEE 754 binary128 overflow but excluding underflow)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html#Integers-implementation)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html#g_t_005f_005fint128)")
(echo "(https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format#IEEE_754_quadruple-precision_binary_floating-point_format:_binary128)")
(define-fun MAX_MAX_INT () Int 9223372036854775807)  ;RangeDegradeMAX
(declare-fun MAX_INT () Int)                  ;RangeDegradeParam
(define-fun MIN_MAX_INT () Int 0)                     ;RangeDegradeMIN
(define-fun MIN_INT () Int (- (- MAX_INT) 1))
(define-fun MAX_REAL () Real (* (^ 2.0 1023) (- 2.0 (^ 2.0 (- 52)))))
(define-fun MIN_REAL () Real (- MAX_REAL))
;avoiding +/-/*/division/modulo overflow
(define-fun add_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (+ _1 _2))(<= (+ _1 _2) MAX_INT)
	))
(define-fun sub_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (- _1 _2))(<= (- _1 _2) MAX_INT)
))
(define-fun mul_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (* _1 _2))(<= (* _1 _2) MAX_INT)
))
(define-fun div_guard ((_1 Int)(_2 Int)) Bool (and 
	(not (= _2 0))
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
))
(define-fun mod_guard ((_1 Int)(_2 Int)) Bool (and 
	(div_guard _1 _2)
))
(declare-datatypes (PT_) ((Pointer 
				NULL
				Void
				(prim (value PT_))
				(ptr (addr Pointer)))))
(declare-sort PT)
(declare-sort Void)
(declare-fun pt2i ((Pointer PT)) Int)
(declare-fun i2pt (Int) (Pointer PT))
(declare-fun r2pt (Real) (Pointer PT))
(declare-fun b2pt (Bool) (Pointer PT))
(define-fun point ((_p (Pointer PT))) (Pointer PT)
				  (ite (is-ptr _p) (addr _p) _p) 
) 
(declare-fun depoint (PT) (Pointer PT))
(declare-const _v PT)
(declare-const _p (Pointer PT))
(assert (iff (= (depoint _v) _p) (= _v (value _p))))

(declare-fun i_THREAD1_62_2351_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__t_62_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun i_2_FUNCTION_i_2 () Int)
(declare-fun _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__chunk_62_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__chunk_62_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun _chunk_size_62_DRB010-lastprivatemissing-var-yes_c__chunk_size_62_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun i_THREAD2_62_2351_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun i_FUNCTION_62_2351_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun _t_62_DRB010-lastprivatemissing-var-yes_c_FUNCTION__t_62_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun x_FUNCTION_63_DRB010-lastprivatemissing-var-yes_c () Int)
(declare-fun _nthreads__nthreads () Int)
(define-fun main ((argc_54_DRB010-lastprivatemissing-var-yes_c_54_DRB010-lastprivatemissing-var-yes_c Int)(argv_54_DRB010-lastprivatemissing-var-yes_c (Pointer PT))) Int 0)
(declare-fun atoi (Str) Int)

(define-fun ParallelCondition () Bool (and 

(and (and (<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c) (not (= _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__chunk_62_DRB010-lastprivatemissing-var-yes_c _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__chunk_62_DRB010-lastprivatemissing-var-yes_c)) (< _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__t_62_DRB010-lastprivatemissing-var-yes_c _nthreads__nthreads) (<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__t_62_DRB010-lastprivatemissing-var-yes_c) (not (= _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__t_62_DRB010-lastprivatemissing-var-yes_c _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c)) (< 0 _t_62_DRB010-lastprivatemissing-var-yes_c_FUNCTION__t_62_DRB010-lastprivatemissing-var-yes_c _nthreads__nthreads) (< _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c _nthreads__nthreads)) (<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT) (<= 1 _nthreads__nthreads MAX_INT) (<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_FUNCTION__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT) (<= 0 _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__chunk_62_DRB010-lastprivatemissing-var-yes_c MAX_INT) (<= 0 _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__chunk_62_DRB010-lastprivatemissing-var-yes_c MAX_INT) (<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT))
(<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT)
(<= 1 _nthreads__nthreads MAX_INT)
(<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_FUNCTION__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT)
(<= 0 _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD1__chunk_62_DRB010-lastprivatemissing-var-yes_c MAX_INT)
(<= 0 _chunk_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__chunk_62_DRB010-lastprivatemissing-var-yes_c MAX_INT)
(<= 0 _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT)
))

;_LB,     _1,    _UB
(define-fun InCarryInRange ((_1 Int)(_LB Int)(_UB Int)) Bool (and
  (<= _LB _1)(<= _1 _UB)
))
(define-fun InCarryInRangeUB ((_1 Int)(_UB Int)) Bool (or
  (= _1 _UB)
  (< _1 _UB)
))
(define-fun InCarryInRangeLB ((_1 Int)(_LB Int)) Bool (or
  (= _1 _LB)
  (> _1 _LB)
))

(echo "Range down-grade...")
;RangeDegradeUB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeUB _1 9223372036854775807))
;RangeDegradeIn(define-fun InRange ((_1 Int)) Bool (InCarryInRange _1 0 9223372036854775807))
;RangeDegradeLB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeLB _1 0))
;RangeDegradeParams(assert (InRange _nthreads__nthreads))

(assert ParallelCondition)

(assert (<= MIN_INT x_FUNCTION_63_DRB010-lastprivatemissing-var-yes_c MAX_INT))
(assert (= i_FUNCTION_62_2351_DRB010-lastprivatemissing-var-yes_c (+ i_2_FUNCTION_i_2 1)))
(assert (= x_FUNCTION_63_DRB010-lastprivatemissing-var-yes_c i_FUNCTION_62_2351_DRB010-lastprivatemissing-var-yes_c))
(assert (<= 0 i_THREAD1_62_2351_DRB010-lastprivatemissing-var-yes_c 9999))
(assert (<= 0 i_THREAD2_62_2351_DRB010-lastprivatemissing-var-yes_c 9999))
(assert (<= MIN_INT _t_62_DRB010-lastprivatemissing-var-yes_c_THREAD2__t_62_DRB010-lastprivatemissing-var-yes_c MAX_INT))

(check-sat)
(get-model)
(exit)