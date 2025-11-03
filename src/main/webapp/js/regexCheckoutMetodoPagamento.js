document.getElementById("modifica-pagamento-form").addEventListener('submit', function (event) {
    let valido = document.getElementsByClassName("non-valido")[0];
    valido.innerHTML = "";

    let nome = document.getElementById("nomeCartaNuova");
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

    let cognome = document.getElementById("cognomeCartaNuova");
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

    let CVV = document.getElementById("CVVNuovo");
    let CVVVal = CVV.value
    const regCVV = /^\d{3,4}$/;

    if(!regCVV.test(CVVVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato CVV non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let carta = document.getElementById("numCartaNuova");
    let cartaVal = carta.value
    const regVia = /^(?:4\d{12}(?:\d{3})?|5[1-5]\d{14})$/

    if(!regVia.test(cartaVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato carta non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }
});