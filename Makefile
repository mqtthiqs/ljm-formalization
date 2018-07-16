DIRS = Metalib Stlc LJm

all:
	@echo Building Metalib...
	(cd Metalib; make; make install; make doc)
	@echo Building Stlc...
	(cd Stlc; make; make install; make html)
	@echo Building LJm...
	(cd LJm; make; make html)

clean:
	@set -e; for d in $(DIRS); \
                   do echo Cleaning $$d...; \
                   $(MAKE) -C $$d clean; \
                 done
