package model.misura;

public class MisuraBean {

    private /*@ spec_public @*/ int IDMaglietta;
    private /*@ spec_public @*/ int quantita;
    private /*@ spec_public nullable @*/ String taglia;

    /*@ public invariant IDMaglietta >= 0;
      @ public invariant quantita >= 0;
      @*/

    /*@ public normal_behavior
      @ ensures true;
      @ assignable \nothing;
      @*/
    public MisuraBean() {}

    /*@ public normal_behavior
      @ requires IDMaglietta >= 0;
      @ requires quantita >= 0;
      @ assignable \everything;
      @ ensures this.IDMaglietta == IDMaglietta;
      @ ensures this.quantita == quantita;
      @ ensures this.taglia == taglia;
      @*/
    public MisuraBean(int IDMaglietta, int quantita, /*@ nullable @*/ String taglia) {
        this.IDMaglietta = IDMaglietta;
        this.quantita = quantita;
        this.taglia = taglia;
    }

    /*@ public normal_behavior
      @ ensures \result == IDMaglietta;
      @ assignable \nothing;
      @ pure
      @*/
    public int getIDMaglietta() {
        return IDMaglietta;
    }

    /*@ public normal_behavior
      @ requires IDMaglietta >= 0;
      @ assignable this.IDMaglietta;
      @ ensures this.IDMaglietta == IDMaglietta;
      @*/
    public void setIDMaglietta(int IDMaglietta) {
        this.IDMaglietta = IDMaglietta;
    }

    /*@ public normal_behavior
      @ ensures \result == taglia;
      @ assignable \nothing;
      @ pure
      @*/
    public /*@ nullable @*/ String getTaglia() {
        return taglia;
    }

    /*@ public normal_behavior
      @ assignable this.taglia;
      @ ensures this.taglia == taglia;
      @*/
    public void setTaglia(/*@ nullable @*/ String taglia) {
        this.taglia = taglia;
    }

    /*@ public normal_behavior
      @ ensures \result == quantita;
      @ assignable \nothing;
      @ pure
      @*/
    public int getQuantita() {
        return quantita;
    }

    /*@ public normal_behavior
      @ requires quantita >= 0;
      @ assignable this.quantita;
      @ ensures this.quantita == quantita;
      @*/
    public void setQuantita(int quantita) {
        this.quantita = quantita;
    }

    // Skip ESC verification for toString(): string concatenations can generate heavy SMT queries.
    //@ skipesc
    @Override
    public String toString() {
        return "MisuraBean{" +
                "IDMaglietta=" + IDMaglietta +
                ", quantita=" + quantita +
                ", taglia='" + taglia + '\'' +
                '}';
    }
}