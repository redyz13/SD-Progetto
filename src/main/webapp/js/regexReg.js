document.getElementById("sform").addEventListener('submit', function (event) {
    let valido = document.getElementsByClassName("non-valida")[0];
    valido.innerHTML = "";

    let email = document.getElementById("emailReg");
    let valEmail = email.value
    const reg = /^[a-zA-Z0-9._%-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,4}$/;

    if(!reg.test(valEmail)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato email non valido");
        valido.appendChild(textNode);
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let password = document.getElementById("passwordReg");
    let passwordVal = password.value
    const regPass = /^[A-Za-z0-9.]{3,16}$/;

    if(!regPass.test(passwordVal)) {
        event.preventDefault();
        let textNode = document.createTextNode("Formato password non valido");
        valido.appendChild(textNode);
        document.createElement("br");
        let br = document.createElement("br");
        valido.appendChild(br);
    }

    let nome = document.getElementById("nomeReg");
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

    let cognome = document.getElementById("cognomeReg");
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
});
