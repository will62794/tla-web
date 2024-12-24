serve:
	python3 -m http.server

open:
	open http://localhost:8000

test:
	cd specs/with_state_graphs && bash gen_state_graphs.sh