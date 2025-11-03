document.getElementById("aggiungi-ordine").addEventListener('submit', function (event) {
    let valido = document.getElementsByClassName("non-valida")[0];
    valido.innerHTML = "";

    let nome = document.getElementById("nome-spedizione");
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

    let cognome = document.getElementById("cognome-spedizione");
    let cognomeVal = cognome.value
    const regCognome = /^[A-Za-z]{2,30}$/;

    if(!regCognome.test(cognomeVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato cognome non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let cap = document.getElementById("cap-spedizione");
    let capVal = cap.value
    const regCap = /^\d{5}$/

    if(!regCap.test(capVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato cap non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let citta = document.getElementById("citta-spedizione");
    let cittaVal = citta.value
    const regCitta = /^[A-Za-z]{2,30}$/;

    if(!regCitta.test(cittaVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato città non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let via = document.getElementById("via-spedizione");
    let viaVal = via.value
    const regVia = /^[A-Za-z]{2,30}$/;

    if(!regVia.test(viaVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato via non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }
});