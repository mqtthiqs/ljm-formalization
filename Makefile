DIRS = Metalib ELambda LambdaJm Lambda

all:
	for d in $(DIRS); do \
	  make -C $$d all install; \
	done

clean:
	for d in $(DIRS); do \
	  $(MAKE) -C $$d clean; \
	done
