function openPopUpIndirizzo() {
	let box = document.getElementsByClassName("modifica-indirizzo")[0];
	box.classList.add("activeModifica");

	let overlay = document.getElementById("overlayIndirizzo")
	overlay.classList.add("activeOverlay");

	document.getElementById("defNav").style.backgroundColor = "transparent";
}

function closePopUpIndirizzo() {
	let box = document.getElementsByClassName("modifica-indirizzo")[0];
	box.classList.remove("activeModifica");

	let overlay = document.getElementById("overlayIndirizzo");
	overlay.classList.remove("activeOverlay");

	document.getElementById("defNav").style.backgroundColor = "white";

}