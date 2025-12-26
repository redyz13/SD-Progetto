package model.ordine;

import java.time.LocalDate;

public class OrdineBean {

    // Make fields "visible" to JML specifications of public methods (spec_public).
    private /*@ spec_public @*/ int ID;

    private /*@ spec_public nullable @*/ String username;
    private /*@ spec_public nullable @*/ String cap;
    private /*@ spec_public nullable @*/ String via;
    private /*@ spec_public nullable @*/ String citta;
    private /*@ spec_public nullable @*/ String nomeConsegna;
    private /*@ spec_public nullable @*/ String cognomeConsegna;

    private /*@ spec_public nullable @*/ LocalDate dataConsegna;
    private /*@ spec_public nullable @*/ LocalDate dataOrdine;

    private /*@ spec_public @*/ float prezzoTotale;

    /*@ public invariant ID >= 0;
      @ public invariant prezzoTotale >= 0.0f;
      @*/

    /*@ public normal_behavior
      @ ensures \result == ID;
      @ assignable \nothing;
      @ pure
      @*/
    public int getID() {
        return ID;
    }

    /*@ public normal_behavior
      @ requires ID >= 0;
      @ assignable this.ID;
      @ ensures this.ID == ID;
      @*/
    public void setID(int ID) {
        this.ID = ID;
    }

    /*@ public normal_behavior
      @ ensures \result == username;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getUsername() {
        return username;
    }

    /*@ public normal_behavior
      @ assignable this.username;
      @ ensures this.username == username;
      @*/
    public void setUsername(/*@ nullable @*/ String username) {
        this.username = username;
    }

    /*@ public normal_behavior
      @ ensures \result == cap;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getCap() {
        return cap;
    }

    /*@ public normal_behavior
      @ assignable this.cap;
      @ ensures this.cap == cap;
      @*/
    public void setCap(/*@ nullable @*/ String cap) {
        this.cap = cap;
    }

    /*@ public normal_behavior
      @ ensures \result == nomeConsegna;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getNomeConsegna() {
        return nomeConsegna;
    }

    /*@ public normal_behavior
      @ assignable this.nomeConsegna;
      @ ensures this.nomeConsegna == nomeConsegna;
      @*/
    public void setNomeConsegna(/*@ nullable @*/ String nomeConsegna) {
        this.nomeConsegna = nomeConsegna;
    }

    /*@ public normal_behavior
      @ ensures \result == cognomeConsegna;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getCognomeConsegna() {
        return cognomeConsegna;
    }

    /*@ public normal_behavior
      @ assignable this.cognomeConsegna;
      @ ensures this.cognomeConsegna == cognomeConsegna;
      @*/
    public void setCognomeConsegna(/*@ nullable @*/ String cognomeConsegna) {
        this.cognomeConsegna = cognomeConsegna;
    }

    /*@ public normal_behavior
      @ ensures \result == via;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getVia() {
        return via;
    }

    /*@ public normal_behavior
      @ assignable this.via;
      @ ensures this.via == via;
      @*/
    public void setVia(/*@ nullable @*/ String via) {
        this.via = via;
    }

    /*@ public normal_behavior
      @ ensures \result == citta;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getCitta() {
        return citta;
    }

    /*@ public normal_behavior
      @ assignable this.citta;
      @ ensures this.citta == citta;
      @*/
    public void setCitta(/*@ nullable @*/ String citta) {
        this.citta = citta;
    }

    /*@ public normal_behavior
      @ ensures \result == dataConsegna;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ LocalDate getDataConsegna() {
        return dataConsegna;
    }

    /*@ public normal_behavior
      @ assignable this.dataConsegna;
      @ ensures this.dataConsegna == dataConsegna;
      @*/
    public void setDataConsegna(/*@ nullable @*/ LocalDate dataConsegna) {
        this.dataConsegna = dataConsegna;
    }

    /*@ public normal_behavior
      @ ensures \result == dataOrdine;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ LocalDate getDataOrdine() {
        return dataOrdine;
    }

    /*@ public normal_behavior
      @ assignable this.dataOrdine;
      @ ensures this.dataOrdine == dataOrdine;
      @*/
    public void setDataOrdine(/*@ nullable @*/ LocalDate dataOrdine) {
        this.dataOrdine = dataOrdine;
    }

    /*@ public normal_behavior
      @ ensures \result == prezzoTotale;
      @ assignable \nothing;
      @ pure
      @*/
    public float getPrezzoTotale() {
        return prezzoTotale;
    }

    /*@ public normal_behavior
      @ requires prezzoTotale >= 0.0f;
      @ assignable this.prezzoTotale;
      @ ensures this.prezzoTotale == prezzoTotale;
      @*/
    public void setPrezzoTotale(float prezzoTotale) {
        this.prezzoTotale = prezzoTotale;
    }

    // Skip ESC verification for toString(): string concatenations can generate heavy SMT queries.
    //@ skipesc
    @Override
    public String toString() {
        return "OrdineBean{" +
                "username='" + username + '\'' +
                ", cap='" + cap + '\'' +
                ", via='" + via + '\'' +
                ", citta='" + citta + '\'' +
                ", dataConsegna=" + dataConsegna +
                ", dataOrdine=" + dataOrdine +
                ", prezzoTotale=" + prezzoTotale +
                '}';
    }
}
