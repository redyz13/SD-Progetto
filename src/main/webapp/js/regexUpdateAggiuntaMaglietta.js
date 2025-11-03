document.getElementById("update").addEventListener('submit', function (event) {
    let valido = document.getElementsByClassName("non-valido")[0];
    valido.innerHTML = "";

    let float = document.getElementById("prezzo");
    let floatVal = float.value
    const regFloat = /^[+-]?\d+(\.\d+)?$/

    if(!regFloat.test(floatVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato del prezzo non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let iva = document.getElementById("iva");
    let ivaVal  = iva.value
    const regIva = /^\d{2}/;

    if(!regIva.test(ivaVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato iva non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let nome = document.getElementById("nome");
    let nomeVal = nome.value
    const regNome = /^[A-Za-z]{2,30}$/;

    if(!regNome.test(nomeVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato nome non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }
});