#lang eopl

;; Especificación léxica
(define especificacion-lexica
  '(
    (espacio-blanco (whitespace) skip)
    (comentario ("%" (arbno (not #\newline))) skip)
    (identificador (letter (arbno (or letter digit "?" "$"))) symbol)
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    (numero (digit (arbno digit) "." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit) "." digit (arbno digit)) number)
  ))

;; Especificación gramatical
(define especificacion-gramatical
  '(
    (programa (expresion) a-program)
    (expresion (numero) lit-exp)
    (expresion (identificador) var-exp)
    ;; Condicionales
    (expresion ("true") true-exp)
    (expresion ("false") false-exp)
    (expresion ("if" expresion "then" expresion "else" expresion) if-exp)
    ;; Ligaduras locales
    (expresion ("let" (arbno identificador "=" expresion) "in" expresion) let-exp)
    ;; Procedimientos
    (expresion ("proc" "(" (separated-list identificador ",") ")" expresion) proc-exp)
    (expresion ("(" expresion (arbno expresion) ")") app-exp)
    ;; Ligaduras recursivas
    (expresion ("letrec" (arbno identificador "(" (separated-list identificador ",") ")" "=" expresion) "in" expresion) letrec-exp) 
    ;; Secuencias
    (expresion ("begin" expresion (arbno ";" expresion) "end") begin-exp)
    ;; Primitivas
    (expresion (primitiva "(" (separated-list expresion ",") ")") prim-exp)
    (primitiva ("+") sum-prim)
    (primitiva ("-") minus-prim)
    (primitiva ("*") mult-prim)
    (primitiva ("/") div-prim)
    (primitiva ("add1") add-prim)
    (primitiva ("sub1") sub-prim)
    ;; Primitivas booleanas
    (primitiva (">") mayor-prim)
    (primitiva (">=") mayorigual-prim)
    (primitiva ("<") menor-prim)
    (primitiva ("<=") menorigual-prim)
    (primitiva ("==") igual-prim)
  ))

;; Creación de los datatypes automáticamente
(sllgen:make-define-datatypes especificacion-lexica especificacion-gramatical)

;; Evaluar programa
(define evaluar-programa
  (lambda (pgm)
    (cases programa pgm
      (a-program (exp) (evaluar-expresion exp ambiente-inicial)))))

;; Definición de ambientes
(define-datatype ambiente ambiente?
  (ambiente-vacio)
  (ambiente-extendido
   (lids (list-of symbol?))
   (lvalue (list-of any?))
   (old-env ambiente?)))

(define ambiente-extendido
  (lambda (lids lvalue old-env)
    (ambiente-extendido lids lvalue old-env)))

;; Aplicar ambiente
(define apply-env
  (lambda (env var)
    (cases ambiente env
      (ambiente-vacio () (eopl:error "No se encuentra la variable " var))
      (ambiente-extendido (lids lvalue old-env)
                          (let ((pos (list-index var lids)))
                            (if pos
                                (list-ref lvalue pos)
                                (apply-env old-env var)))))))

;; Helper para índices en listas
(define list-index
  (lambda (item lst)
    (let loop ((lst lst) (idx 0))
      (cond
        [(null? lst) #f]
        [(equal? (car lst) item) idx]
        [else (loop (cdr lst) (+ idx 1))]))))

;; Evaluar expresiones
(define evaluar-expresion
  (lambda (exp amb)
    (cases expresion exp
      (lit-exp (dato) dato)
      (var-exp (id) (apply-env amb id))
      ;; Booleanos
      (true-exp () #true)
      (false-exp () #false)
      ;; Primitivas
      (prim-exp (prim args)
                (let ((lista-numeros (map (lambda (x) (evaluar-expresion x amb)) args)))
                  (evaluar-primitiva prim lista-numeros)))
      ;; Condicionales
      (if-exp (condicion hace-verdadero hace-falso)
              (if (evaluar-expresion condicion amb)
                  (evaluar-expresion hace-verdadero amb)
                  (evaluar-expresion hace-falso amb)))
      ;; Ligaduras locales
      (let-exp (ids rands body)
               (let ((lvalues (map (lambda (x) (evaluar-expresion x amb)) rands)))
                 (evaluar-expresion body (ambiente-extendido ids lvalues amb))))
      ;; Procedimientos
      (proc-exp (ids body) (closure ids body amb))
      (app-exp (rator rands)
               (let ((lrands (map (lambda (x) (evaluar-expresion x amb)) rands))
                     (procV (evaluar-expresion rator amb)))
                 (if (procval? procV)
                     (cases procval procV
                       (closure (lid body old-env)
                                (if (= (length lid) (length lrands))
                                    (evaluar-expresion body
                                                       (ambiente-extendido lid lrands old-env))
                                    (eopl:error "Número incorrecto de argumentos"))))
                     (eopl:error "No es un procedimiento válido"))))
      ;; Ligaduras recursivas
      (letrec-exp (procnames idss cuerpos cuerpo-letrec)
                  (let ((procedures (map (lambda (ids cuerpo)
                                           (closure ids cuerpo amb)) idss cuerpos)))
                    (evaluar-expresion cuerpo-letrec
                                       (ambiente-extendido procnames procedures amb))))
      ;; Secuencias
      (begin-exp (exp lexp)
                 (let ((val (evaluar-expresion exp amb)))
                   (if (null? lexp)
                       val
                       (evaluar-expresion (begin-exp (car lexp) (cdr lexp)) amb)))))))

;; Evaluar primitivas
(define evaluar-primitiva
  (lambda (prim lval)
    (cases primitiva prim
      (sum-prim () (operacion-prim lval + 0))
      (minus-prim () (operacion-prim lval - 0))
      (mult-prim () (operacion-prim lval * 1))
      (div-prim () (operacion-prim lval / 1))
      (add-prim () (+ (car lval) 1))
      (sub-prim () (- (car lval) 1))
      (mayor-prim () (> (car lval) (cadr lval)))
      (mayorigual-prim () (>= (car lval) (cadr lval)))
      (menor-prim () (< (car lval) (cadr lval)))
      (menorigual-prim () (<= (car lval) (cadr lval)))
      (igual-prim () (= (car lval) (cadr lval))))))

(define operacion-prim
  (lambda (lval op term)
    (cond
      [(null? lval) term]
      [else (op (car lval) (operacion-prim (cdr lval) op term))])))

;; Procedimientos
(define-datatype procval procval?
  (closure (lid (list-of symbol?))
           (body expresion?)
           (amb-creation ambiente?)))

;; Ambiente inicial
(define ambiente-inicial
  (ambiente-extendido '(x y z) '(4 2 5)
                      (ambiente-extendido '(a b c) '(4 5 6)
                                          (ambiente-vacio))))

;; Interpretador
(define interpretador
  (sllgen:make-rep-loop "-->" evaluar-programa
                        (sllgen:make-stream-parser
                         especificacion-lexica especificacion-gramatical)))

(interpretador)
