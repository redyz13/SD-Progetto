function openPopUp() {
	let box = document.getElementsByClassName("modifica-pagamento")[0];
	box.classList.add("activeModifica");

	let overlay = document.getElementById("overlay")
	overlay.classList.add("activeOverlay");
}

function closePopUp() {
	let box = document.getElementsByClassName("modifica-pagamento")[0];
	box.classList.remove("activeModifica");

	let overlay = document.getElementById("overlay");
	overlay.classList.remove("activeOverlay");
}