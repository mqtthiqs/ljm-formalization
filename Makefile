DIRS = Metalib Stlc LJm

all:
	@echo Building Metalib...
	(cd Metalib; make; make install)
	@echo Building Stlc...
	(cd Stlc; make; make install)
	@echo Building LJm...
	(cd LJm; make)

clean:
	@set -e; for d in $(DIRS); \
                   do echo Cleaning $$d...; \
                   $(MAKE) -C $$d clean; \
                 done
