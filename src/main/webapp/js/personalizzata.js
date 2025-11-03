function changeColor() {
	let sfondo = document.getElementById("tshirt-backgroundpicture");
	switch (document.getElementById("tshirt-color").value) {
	case "Viola":
		sfondo.style.backgroundColor = "#cb0efa";
		break;
	case "Bianco":
		sfondo.style.backgroundColor = "#fff";
		break;
	case "Nero":
		sfondo.style.backgroundColor = "#000";
		break;
	case "Rosso":
		sfondo.style.backgroundColor = "#f90d0d";
		break;
	case "Verde":
		sfondo.style.backgroundColor = "#38b810";
		break;
	default:
		break;

	}
}

function addImage() {
	document.getElementById("tshirt-new").src = document
			.getElementById("tshirt-design").value;
	document.getElementById("rmImage").style.display = 'block';

}

function addNew() {
	let fileInput = document.getElementById("tshirt-custompicture");
	let file = fileInput.files[0];

	if (file) {
		let reader = new FileReader();
		reader.onload = function(e) {
			let newSrc = e.target.result;
			let tshirtNewElement = document.getElementById("tshirt-new");
			tshirtNewElement.setAttribute('src', newSrc);
		};
		reader.readAsDataURL(file);
		document.getElementById("rmImage").style.display = 'block';
	}
}