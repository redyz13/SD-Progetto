package model.acquisto;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.sql.DataSource;
import java.lang.reflect.Method;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.Iterator;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class AcquistoDAOTest {

    private AcquistoDAO dao;

    private DataSource dsMock;
    private Connection connMock;
    private PreparedStatement psMock;
    private ResultSet rsMock;

    @BeforeEach
    void setup() throws Exception {
        dsMock = mock(DataSource.class);
        connMock = mock(Connection.class);
        psMock = mock(PreparedStatement.class);
        rsMock = mock(ResultSet.class);

        dao = new AcquistoDAO(dsMock);

        when(dsMock.getConnection()).thenReturn(connMock);
        when(connMock.prepareStatement(anyString())).thenReturn(psMock);
        when(psMock.executeUpdate()).thenReturn(1);
        when(psMock.executeQuery()).thenReturn(rsMock);
    }

    // -------- Test doRetrieveByKey() --------

    // {code_valido, rs_una_riga, db_ok}
    @Test
    void doRetrieveByKey_ok_setsFields() throws Exception {
        when(rsMock.getInt("IDAcquisto")).thenReturn(1);
        when(rsMock.getInt("IDOrdine")).thenReturn(10);
        when(rsMock.getInt("IDMaglietta")).thenReturn(20);
        when(rsMock.getInt("quantita")).thenReturn(2);
        when(rsMock.getString("immagine")).thenReturn("img.png");
        when(rsMock.getFloat("prezzoAq")).thenReturn(9.99f);
        when(rsMock.getInt("ivaAq")).thenReturn(22);
        when(rsMock.getString("taglia")).thenReturn("M");

        AcquistoBean out = dao.doRetrieveByKey(1);

        assertNotNull(out);
        assertEquals(1, out.getIDAcquisto());
        assertEquals(10, out.getIDOrdine());
        assertEquals(20, out.getIDMaglietta());
        assertEquals(2, out.getQuantita());
        assertEquals("img.png", out.getImmagine());
        assertEquals(9.99f, out.getPrezzoAq(), 0.0001f);
        assertEquals(22, out.getIvaAq());
        assertEquals("M", out.getTaglia());

        verify(psMock).setInt(1, 1);
        verify(psMock).executeQuery();
    }

    // {db_exception}
    @Test
    void doRetrieveByKey_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));
        assertThrows(SQLException.class, () -> dao.doRetrieveByKey(1));
    }

    // -------- Test doRetrieveByOrdine() --------

    // {idOrdine_valido, rs_piu_righe, db_ok}
    @Test
    void doRetrieveByOrdine_dueRighe_valuesAreMapped() throws Exception {
        AtomicInteger calls = new AtomicInteger(0);
        when(rsMock.next()).thenAnswer(inv -> {
            int c = calls.incrementAndGet();
            if (c == 1) return true;
            if (c == 2) return true;
            if (c == 3) return false;
            throw new AssertionError("infinite loop on ResultSet.next()");
        });

        when(rsMock.getInt("IDAcquisto")).thenReturn(1, 2);
        when(rsMock.getInt("IDOrdine")).thenReturn(10, 10);
        when(rsMock.getInt("IDMaglietta")).thenReturn(20, 21);
        when(rsMock.getInt("quantita")).thenReturn(2, 3);
        when(rsMock.getString("immagine")).thenReturn("a.png", "b.png");
        when(rsMock.getFloat("prezzoAq")).thenReturn(9.99f, 19.50f);
        when(rsMock.getInt("ivaAq")).thenReturn(22, 10);
        when(rsMock.getString("taglia")).thenReturn("M", "L");

        Collection<AcquistoBean> res = dao.doRetrieveByOrdine(10);

        assertEquals(2, res.size());

        Iterator<AcquistoBean> it = res.iterator();
        AcquistoBean a1 = it.next();
        AcquistoBean a2 = it.next();

        assertEquals(1, a1.getIDAcquisto());
        assertEquals(10, a1.getIDOrdine());
        assertEquals(20, a1.getIDMaglietta());
        assertEquals(2, a1.getQuantita());
        assertEquals("a.png", a1.getImmagine());
        assertEquals(9.99f, a1.getPrezzoAq(), 0.0001f);
        assertEquals(22, a1.getIvaAq());
        assertEquals("M", a1.getTaglia());

        assertEquals(2, a2.getIDAcquisto());
        assertEquals(10, a2.getIDOrdine());
        assertEquals(21, a2.getIDMaglietta());
        assertEquals(3, a2.getQuantita());
        assertEquals("b.png", a2.getImmagine());
        assertEquals(19.50f, a2.getPrezzoAq(), 0.0001f);
        assertEquals(10, a2.getIvaAq());
        assertEquals("L", a2.getTaglia());

        verify(psMock).setInt(1, 10);
        verify(psMock).executeQuery();
    }

    // {idOrdine_valido, rs_vuoto, db_ok}
    @Test
    void doRetrieveByOrdine_zeroRighe_returnsEmpty() throws Exception {
        when(rsMock.next()).thenReturn(false);

        Collection<AcquistoBean> res = dao.doRetrieveByOrdine(10);

        assertNotNull(res);
        assertTrue(res.isEmpty());

        verify(psMock).setInt(1, 10);
        verify(psMock).executeQuery();
    }

    // {db_exception}
    @Test
    void doRetrieveByOrdine_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));
        assertThrows(SQLException.class, () -> dao.doRetrieveByOrdine(10));
    }

    // -------- Test doRetriveAll() --------

    // {order_ignored, returns_modifiable_empty_list}
    @Test
    void doRetriveAll_returnsModifiableEmptyList() {
        Collection<AcquistoBean> res = dao.doRetriveAll(null);

        assertNotNull(res);
        assertTrue(res.isEmpty());

        assertDoesNotThrow(() -> res.add(new AcquistoBean()));
        assertEquals(1, res.size());
    }

    // -------- Test doSave() --------

    // {acquisto_valido, db_ok}
    @Test
    void doSave_ok_setsAllParamsAndExecutes() throws Exception {
        AcquistoBean a = mock(AcquistoBean.class);
        when(a.getIDOrdine()).thenReturn(10);
        when(a.getIDMaglietta()).thenReturn(20);
        when(a.getQuantita()).thenReturn(2);
        when(a.getImmagine()).thenReturn("img.png");
        when(a.getPrezzoAq()).thenReturn(9.99f);
        when(a.getIvaAq()).thenReturn(22);
        when(a.getTaglia()).thenReturn("M");

        dao.doSave(a);

        verify(psMock).setInt(1, 10);
        verify(psMock).setInt(2, 20);
        verify(psMock).setInt(3, 2);
        verify(psMock).setString(4, "img.png");
        verify(psMock).setFloat(5, 9.99f);
        verify(psMock).setInt(6, 22);
        verify(psMock).setString(7, "M");
        verify(psMock).executeUpdate();
    }

    // {db_exception}
    @Test
    void doSave_dbException_propagatesSQLException() throws Exception {
        when(dsMock.getConnection()).thenThrow(new SQLException("db fail"));

        AcquistoBean a = mock(AcquistoBean.class);
        when(a.getIDOrdine()).thenReturn(10);
        when(a.getIDMaglietta()).thenReturn(20);
        when(a.getQuantita()).thenReturn(2);
        when(a.getImmagine()).thenReturn("img.png");
        when(a.getPrezzoAq()).thenReturn(9.99f);
        when(a.getIvaAq()).thenReturn(22);
        when(a.getTaglia()).thenReturn("M");

        assertThrows(SQLException.class, () -> dao.doSave(a));
    }

    // -------- Test doUpdate() --------

    // {operation_not_supported}
    @Test
    void doUpdate_doesNothing() {
        AcquistoBean a = new AcquistoBean();
        assertDoesNotThrow(() -> dao.doUpdate(a));
    }

    // -------- Test doDelete() --------

    // {operation_not_supported}
    @Test
    void doDelete_alwaysFalse() {
        assertFalse(dao.doDelete(1));
    }

    // -------- Test setAcquisto() --------

    // {rs_valori_normali}
    @Test
    void setAcquisto_ok_setsAllFields() throws Exception {
        when(rsMock.getInt("IDAcquisto")).thenReturn(1);
        when(rsMock.getInt("IDOrdine")).thenReturn(10);
        when(rsMock.getInt("IDMaglietta")).thenReturn(20);
        when(rsMock.getInt("quantita")).thenReturn(2);
        when(rsMock.getString("immagine")).thenReturn("img.png");
        when(rsMock.getFloat("prezzoAq")).thenReturn(9.99f);
        when(rsMock.getInt("ivaAq")).thenReturn(22);
        when(rsMock.getString("taglia")).thenReturn("M");

        Method m = AcquistoDAO.class.getDeclaredMethod("setAcquisto", ResultSet.class, AcquistoBean.class);
        m.setAccessible(true);

        AcquistoBean out = new AcquistoBean();
        m.invoke(dao, rsMock, out);

        assertEquals(1, out.getIDAcquisto());
        assertEquals(10, out.getIDOrdine());
        assertEquals(20, out.getIDMaglietta());
        assertEquals(2, out.getQuantita());
        assertEquals("img.png", out.getImmagine());
        assertEquals(9.99f, out.getPrezzoAq(), 0.0001f);
        assertEquals(22, out.getIvaAq());
        assertEquals("M", out.getTaglia());
    }

    // {rs_exception}
    @Test
    void setAcquisto_rsThrows_wrapsInvocationCauseAsSQLException() throws Exception {
        when(rsMock.getInt("IDAcquisto")).thenThrow(new SQLException("boom"));

        Method m = AcquistoDAO.class.getDeclaredMethod("setAcquisto", ResultSet.class, AcquistoBean.class);
        m.setAccessible(true);

        Exception ex = assertThrows(Exception.class, () -> m.invoke(dao, rsMock, new AcquistoBean()));
        assertNotNull(ex.getCause());
        assertTrue(ex.getCause() instanceof SQLException);
        assertTrue(ex.getCause().getMessage().contains("boom"));
    }

    // -------- Test setAcquistoStatement() --------

    // {acquisto_valido, ps_ok}
    @Test
    void setAcquistoStatement_ok_setsAllParams() throws Exception {
        AcquistoBean a = mock(AcquistoBean.class);
        when(a.getIDOrdine()).thenReturn(10);
        when(a.getIDMaglietta()).thenReturn(20);
        when(a.getQuantita()).thenReturn(2);
        when(a.getImmagine()).thenReturn("img.png");
        when(a.getPrezzoAq()).thenReturn(9.99f);
        when(a.getIvaAq()).thenReturn(22);
        when(a.getTaglia()).thenReturn("M");

        Method m = AcquistoDAO.class.getDeclaredMethod("setAcquistoStatement", AcquistoBean.class, PreparedStatement.class);
        m.setAccessible(true);

        m.invoke(dao, a, psMock);

        verify(psMock).setInt(1, 10);
        verify(psMock).setInt(2, 20);
        verify(psMock).setInt(3, 2);
        verify(psMock).setString(4, "img.png");
        verify(psMock).setFloat(5, 9.99f);
        verify(psMock).setInt(6, 22);
        verify(psMock).setString(7, "M");
    }
}
