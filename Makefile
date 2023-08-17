serve:
	python3 -m http.server

test:
	cd specs/with_state_graphs && bash gen_state_graphs.sh