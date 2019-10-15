DEPS::=lib/metalib/Metalib lib/coq-ext-lib
ALL_DEPS::=${DEPS} lib/Coq-Equations
PROJECTS::=dsub fsub

.PHONY: clean deps docs

${PROJECTS}: ${ALL_DEPS} share
	cd $@ && ${MAKE}

.submodules-pulled:
	touch .submodules-pulled

share:${DEPS} lib/Coq-Equations

lib/Coq-Equations: .submodules-pulled
	cd $@ && coq_makefile -f _CoqProject -o Makefile && ${MAKE}

${DEPS} share: .submodules-pulled
	cd $@ && ${MAKE}

docs/index.html:
	cd docs && \
	pandoc index.md -H include.html --no-highlight -T 'Undecidability of D<: and Its Decidable Fragments' -t html --css styling.css -o index.html

docs:
	cd dsub && ${MAKE} doc
	cd fsub && ${MAKE} doc
	cd agda && agda-2.5.4.2 --css Agda.css --html Everything.agda
	mkdir -p docs
	cp -Trf dsub/doc docs/dsub
	cp -Trf fsub/doc docs/fsub
	cp -Trf agda/html docs/agda
	for f in docs/agda/*.html; do python process.py $$f; done
	make docs/index.html

deps: ${ALL_DEPS}

CWD=$(shell pwd)
clean:
	for d in ${ALL_DEPS}; do cd ${CWD}; cd "$$d" && ${MAKE} clean; done
	cd agda/; rm *.agdai
