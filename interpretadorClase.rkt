#lang eopl
(define especificacion-lexica
  '(
    (espacio-blanco (whitespace) skip)
    (comentario ("%" (arbno (not #\newline))) skip)
    (identificador (letter (arbno (or letter digit "?" "$"))) symbol)
    (numero (digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)) number)
    (numero (digit (arbno digit)"." digit (arbno digit)) number)
    (numero ("-" digit (arbno digit)"." digit (arbno digit)) number)
    )
  )


(define especificacion-gramatical
  '(
    (programa (expresion) a-program)
    (expresion (numero) lit-exp)
    (expresion (identificador) var-exp)
    ;;Agregamos la gramática de los condicionales y las ligaduras
    (expresion ("true") true-exp)
    (expresion ("false") false-exp)
    (expresion ("if" expresion "then" expresion "else" expresion) if-exp)
    ;;Ligaduras locales
    (expresion ("let" (arbno identificador "=" expresion) "in" expresion) let-exp)
    ;;Fin de condicionales y ligaduras
    ;;procedimientos
    (expresion ("proc" "(" (separated-list identificador ",") ")" expresion) proc-exp)
    (expresion ("(" expresion (arbno expresion) ")") app-exp)

    ;;fin procedimientos
    ;;procedimientos recursivos
    (expresion ("letrec" (arbno identificador "(" (separated-list identificador ",") ")" "=" expresion) "in" expresion) letrec-exp) 
    ;;fin de procedimientos recursivos

    ;;Asignación
    (expresion ("begin" expresion (arbno ";" expresion) "end") begin-exp)
    (expresion ("set" identificador "=" expresion) set-exp)

    ;;Primitivas
    (expresion (primitiva "(" (separated-list expresion ",") ")") prim-exp)
    (primitiva ("+") sum-prim)
    (primitiva ("-") minus-prim)
    (primitiva ("*") mult-prim)
    (primitiva ("/") div-prim)
    (primitiva ("add1") add-prim)
    (primitiva ("sub1") sub-prim)
    ;;primitivas booleanas
    (primitiva (">") mayor-prim)
    (primitiva (">=") mayorigual-prim)
    (primitiva ("<") menor-prim)
    (primitiva ("<=") menorigual-prim)
    (primitiva ("==") igual-prim)

     ;; Expresiones de listas
    (expresion ("empty") list-empty-exp)
    (expresion ("cons" "(" expresion "," expresion ")") list-cons-exp)
    (expresion ("length" "(" expresion ")") list-length-exp)
    (expresion ("first" "(" expresion ")") list-first-exp)
    (expresion ("rest" "(" expresion ")") list-rest-exp)
    (expresion ("nth" "(" expresion "," expresion ")") list-nth-exp)

    ;; Expresión condicional
    (expresion ("cond" (arbno expresion "==>" expresion) "else" "==>" expresion "end") cond-exp)
  ))
    

;;Creamos los datatypes automaticamente
(sllgen:make-define-datatypes especificacion-lexica especificacion-gramatical)


;;Evaluar programa
(define evaluar-programa
  (lambda (pgm)
    (cases programa pgm
      (a-program (exp) (evaluar-expresion exp ambiente-inicial))
      ))
  )

;;ambientes
(define-datatype ambiente ambiente?
  (ambiente-vacio)
  (ambiente-extendido-ref
   (lids (list-of symbol?))
   (lvalue vector?)
   (old-env ambiente?)))

(define ambiente-extendido
  (lambda (lids lvalue old-env)
    (ambiente-extendido-ref lids (list->vector lvalue) old-env)))

;;Implementación ambiente extendido recursivo

(define ambiente-extendido-recursivo
  (lambda (procnames lidss cuerpos old-env)
    (let
        (
         (vec-clausuras (make-vector (length procnames)))
         )
      (letrec
          (
           (amb (ambiente-extendido-ref procnames vec-clausuras old-env))
           (obtener-clausuras
            (lambda (lidss cuerpos pos)
              (cond
                [(null? lidss) amb]
                [else
                 (begin
                   (vector-set! vec-clausuras pos
                                (closure (car lidss) (car cuerpos) amb))
                   (obtener-clausuras (cdr lidss) (cdr cuerpos) (+ pos 1)))]
                )
              )
            )
           )
        (obtener-clausuras lidss cuerpos 0)
        )
      )
    )
  )


(define apply-env
  (lambda (env var)
    (deref (apply-env-ref env var))))


(define apply-env-ref
  (lambda (env var)
    (cases ambiente env
      (ambiente-vacio () (eopl:error "No se encuentra la variable " var))
      (ambiente-extendido-ref (lid vec old-env)
                          (letrec
                              (
                               (buscar-variable (lambda (lid vec pos)
                                                  (cond
                                                    [(null? lid) (apply-env-ref old-env var)]
                                                    [(equal? (car lid) var) (a-ref pos vec)]
                                                    [else
                                                     (buscar-variable (cdr lid) vec (+ pos 1)  )]
                                                    )
                                                  )
                                                )
                               )
                            (buscar-variable lid vec 0)
                            )
                          
                          )
      
      )
    )
  )

(define ambiente-inicial
  (ambiente-extendido '(x y z) '(4 2 5)
                      (ambiente-extendido '(a b c) '(4 5 6)
                                          (ambiente-vacio))))

;;Evaluar expresion
(define evaluar-expresion
  (lambda (exp amb)
    (cases expresion exp
      (lit-exp (dato) dato)
      (var-exp (id) (apply-env amb id))
      ;;Booleanos
      (true-exp () #true)
      (false-exp () #false)
      ;;Fin booleanos
      (prim-exp (prim args)
                (let
                    (
                     (lista-numeros (map (lambda (x) (evaluar-expresion x amb)) args))
                     )
                  (evaluar-primitiva prim lista-numeros)
                  )
                )
      ;; Expresiones de listas
      (list-empty-exp () '())
      (list-cons-exp (head tail)
                     (let ((head-val (evaluar-expresion head amb))
                           (tail-val (evaluar-expresion tail amb)))
                       (if (list? tail-val)
                           (cons head-val tail-val)
                           (eopl:error "El segundo argumento de cons no es una lista" tail-val))))
      (list-length-exp (lst)
                       (let ((lst-val (evaluar-expresion lst amb)))
                         (if (list? lst-val)
                             (length lst-val)
                             (eopl:error "Argumento de length no es una lista" lst-val))))
      (list-first-exp (lst)
                      (let ((lst-val (evaluar-expresion lst amb)))
                        (if (and (list? lst-val) (not (null? lst-val)))
                            (car lst-val)
                            (eopl:error "Argumento de first no es una lista no vacía" lst-val))))
      (list-rest-exp (lst)
                     (let ((lst-val (evaluar-expresion lst amb)))
                       (if (and (list? lst-val) (not (null? lst-val)))
                           (cdr lst-val)
                           (eopl:error "Argumento de rest no es una lista no vacía" lst-val))))
      (list-nth-exp (lst n)
                    (let ((lst-val (evaluar-expresion lst amb))
                          (n-val (evaluar-expresion n amb)))
                      (if (and (list? lst-val) (integer? n-val) (>= n-val 0) (< n-val (length lst-val)))
                          (list-ref lst-val n-val)
                          (eopl:error "Argumentos inválidos para nth: lista o índice" lst-val n-val))))

      ;; Expresión condicional
      (define (eval-cond-exp cond-exps env)
  (cond
    [(null? cond-exps) (error "No matching condition in cond!")]
    [else
     (let ([first-cond (car cond-exps)])
       (if (and (pair? first-cond) (equal? (car first-cond) 'else))
           (eval-exp (cadr first-cond) env) ; Evaluar el else
           (if (pair? first-cond) ; Validar si es un par condición => valor
               (if (true? (eval-exp (car first-cond) env)) ; Evaluar condición
                   (eval-exp (cadr first-cond) env) ; Evaluar resultado si es verdadero
                   (eval-cond-exp (cdr cond-exps) env)) 
               (error "Malformed cond branch"))))]))

      ;;Condicionales
      (if-exp (condicion hace-verdadero hace-falso)
              (if
               (evaluar-expresion condicion amb) ;;Evaluamos la condición
               (evaluar-expresion hace-verdadero amb) ;;En caso de que sea verdadero
               (evaluar-expresion hace-falso amb) ;;En caso de que sea falso
               )
              )
      ;;Ligaduras locales
      (let-exp (ids rands body)
               (let
                   (
                    (lvalues (map (lambda (x) (evaluar-expresion x amb)) rands))
                    )
                 (evaluar-expresion body (ambiente-extendido ids lvalues amb))
                 )
               )
      ;;procedimientos
      (proc-exp (ids body)
                (closure ids body amb))
      (app-exp (rator rands)
               (let
                   (
                    (lrands (map (lambda (x) (evaluar-expresion x amb)) rands))
                    (procV (evaluar-expresion rator amb))
                    )
                 (if
                  (procval? procV)
                  (cases procval procV
                    (closure (lid body old-env)
                             (if (= (length lid) (length lrands))
                                 (evaluar-expresion body
                                                (ambiente-extendido lid lrands old-env))
                                 (eopl:error "El número de argumentos no es correcto, debe enviar" (length lid)  " y usted ha enviado" (length lrands))
                                 )
                             ))
                  (eopl:error "No puede evaluarse algo que no sea un procedimiento" procV) 
                  )
                 )
               )

      ;;letrec
      (letrec-exp (procnames idss cuerpos cuerpo-letrec)
                  (evaluar-expresion cuerpo-letrec
                                     (ambiente-extendido-recursivo procnames idss cuerpos amb)))

      ;;Asignación
      ;;begin
      (begin-exp (exp lexp)
                 (if
                  (null? lexp)
                  (evaluar-expresion exp amb)
                  (begin
                    (evaluar-expresion exp amb)
                    (letrec
                        (
                         (evaluar-begin (lambda (lexp)
                                          (cond
                                            [(null? (cdr lexp)) (evaluar-expresion (car lexp) amb)]
                                            [else
                                             (begin
                                               (evaluar-expresion (car lexp) amb)
                                               (evaluar-begin (cdr lexp))
                                               )
                                             ]
                                            )
                                          )
                                        )
                         )
                      (evaluar-begin lexp)
                      )
                    )
                  )
                 )
      ;;set
      (set-exp (id exp)
               (begin
                 (setref!
                  (apply-env-ref amb id)
                  (evaluar-expresion exp amb))
                 1)
               )
      )
    

    )
  )

;;Manejo de primitivas
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
      (igual-prim () (= (car lval) (cadr lval)))
      )
    )
  )


(define operacion-prim
  (lambda (lval op term)
    (cond
      [(null? lval) term]
      [else
       (op
        (car lval)
        (operacion-prim (cdr lval) op term))
       ]
      )
    )
  )

;;Definiciones para los procedimientos
(define-datatype procval procval?
  (closure (lid (list-of symbol?))
           (body expresion?)
           (amb-creation ambiente?)))

;;Referencias

(define-datatype referencia referencia?
  (a-ref (pos number?)
         (vec vector?)))

;;Extractor de referencias
(define deref
  (lambda (ref)
    (primitiva-deref ref)))

(define primitiva-deref
  (lambda (ref)
    (cases referencia ref
      (a-ref (pos vec)
             (vector-ref vec pos)))))

;;Asignación/cambio referencias
(define setref!
  (lambda (ref val)
    (primitiva-setref! ref val)))

(define primitiva-setref!
  (lambda (ref val)
    (cases referencia ref
      (a-ref (pos vec)
             (vector-set! vec pos val)))))


;;Interpretador
(define interpretador
  (sllgen:make-rep-loop "-->" evaluar-programa
                        (sllgen:make-stream-parser
                         especificacion-lexica especificacion-gramatical)))


(interpretador)


