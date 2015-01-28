package temp;



/**
 * <!-- Versie 1.3
 *
 * -------------
 * - CHANGELOG -
 * -------------
 *
 * Versie 1.3
 *
 * + Ping/Pong
 * + Name in Chat sent by server
 * + Default port (WARNING)
 * + Error codes documented
 * * fixed leaderboard packet
 * - multitypes
 *
 * Versie 1.2
 *
 * + Protocol.Features
 * + Protocol.Settings
 * * Protocol.Client.CHAT fixed
 *
 * Versie 1.1
 *
 * + Package aangepast naar bruikbaar formaat
 * + Javadocs gelayout voor verbeterde readability.
 *
 * Versie 1.0
 *
 * + Eerste versie protocol
 *
 * -->
*/

/**
 * <h1 id="protocol-ti-2">Protocol TI-2</h1>
 *
 * <p>In dit bestand staat het protocol van werkgroep TI-2 zoals dat op do. 8 januari is afgesproken. </p>
 *
 *
 * <h2 id="1-over-standaarden">1. Over Standaarden</h2>
 *
 * <p>Bij het afspreken van het protocol zijn de volgende standaarden overwogen:</p>
 *
 * <ol>
 *     <li>Objectstream</li>
 *     <li>Printstream</li>
 *     <li>Datastream</li>
 * </ol>
 *
 * <p>Na verschillende keren stemmen is voor de printstream-optie gekozen.  <br>
 *     De stemmingen waren als volgt:</p>
 *
 * <ol>
 *     <li><code>9</code> stemmen voor <code>Datastream</code>, <code>8</code> stemmen voor <code>Printstream</code>, verder geen mening. Ergo: <code>Datastream</code>, met 1 stem winst</li>
 *     <li><code>5</code> stemmen voor <code>Datastream</code>, <code>7</code> stemmen voor <code>Printstream</code>, verder geen mening. Ergo: <code>Printstream</code>, met 2 stemmen winst</li>
 * </ol>
 *
 * <p>Hierop volgen de overwegingen die hierbij in acht zijn genomen.</p>
 *
 *
 * <h3 id="objectstream">Objectstream</h3>
 *
 * <p>Tegen de objectstream zijn de volgende argumenten ingebracht:</p>
 *
 * <ul>
 *     <li>Een objectstream is niet compatible met verschillend geprogrammeerde programma’s.</li>
 *     <li>Een objectstream is heel inefficient.</li>
 * </ul>
 *
 *
 * <h3 id="printstream">Printstream</h3>
 *
 * <p>Voor de printstream zijn de volgende argumenten ingebracht:</p>
 *
 * <ul>
 *     <li>Een printstream is makkelijk te debuggen</li>
 *     <li>Een printstream is makkelijk door mensen te lezen</li>
 * </ul>
 *
 * <p>Tegen de printstream zijn de volgende argumenten ingebracht:</p>
 *
 * <ul>
 *     <li>Een printstream is inefficient in het uitlezen</li>
 *     <li>Een printstream kan gemakkelijk zorgen voor type conflicts</li>
 * </ul>
 *
 *
 * <h3 id="datastream">Datastream</h3>
 *
 * <p>Voor de datastream zijn de volgende argumenten ingebracht:</p>
 *
 * <ul>
 *     <li>Een datastream is heel makkelijk uit te lezen</li>
 *     <li>Een datastream is heel efficient</li>
 *     <li>Een datastream zorgt voor minder type conflicts tussen verschillende programma’s</li>
 * </ul>
 *
 * <p>Tegen de datastream zijn de volgende argumenten ingebracht:</p>
 *
 * <ul>
 *     <li>Een datastream is lastig debuggen</li>
 * </ul>
 *
 *
 * <h2 id="beslissingen">Beslissingen</h2>
 *
 * <p>Omdat niet alle datatypen voor iedereen gelijk zouden zijn, heb ik (Matthias) besloten enkele datatypen zelf vast te leggen. In veel gevallen is het wel mogelijk om het anders te implementeren, maar de typen die ik nu heb neergezet zijn er vanwege gebruiksgemak ingezet.</p>
 *
 *
 * <h3 id="board">Board</h3>
 *
 * <p>Zoals later in dit document zal blijken wordt de boardgrootte doorgegeven met behulp van <code>short</code>s. Dit heb ik besloten zo te doen omdat de maximale array length van Java <code>Integer.MAX_SIZE - 8</code> is in veel JREs. </p>
 *
 * <p>Natuurlijk mag iedereen zijn eigen maximale grootte verder zelf bepalen, maar om compatibiliteit te behouden gebruiken we hier <code>Short.MAX_SIZE</code> als absoluut maximum.</p>
 *
 * <p>Ook heb ik besloten om de waarden in het board in bytes op te slaan. Dit doe ik omdat ik me niet kan voorstellen dat meer dan 255 spelers tegelijk zo’n spel zullen spelen. </p>
 *
 * <p>Een board wordt verstuurd in 1 keer. Een leeg veld heeft de waarde 0. De velden die gevuld zijn hebben de waarde van de speler die daar zijn/haar zet heeft gedaan, deze waarde is het startnummer. <code>Player1 = 1</code>, <code>Player2 = 2</code> … <code>PlayerN = N</code>.</p>
 *
 * <p>De telling van kolommen begint links, en start bij 0 (net als bij een <code>array</code>). Bij een bord van 7 breed heb je dus kolommen <code>0</code>, <code>1</code>, <code>2</code>, <code>3</code>, <code>4</code>, <code>5</code> en <code>6</code> van links naar rechts.</p>
 *
 *
 * <h3 id="player-names">Player Names</h3>
 *
 * <p>Vanwege gebruiksgemak en het vergemakkelijken van het renderen heb ik besloten om de maximale lengte van de naam van een player op 15 karakters te zetten. Dit is in de meeste, zo niet alle, gevallen wel genoeg, en zal door de maximale lengte ook geen problemen meer opleveren door veel te lange usernames in bijvoorbeeld de chat.</p>
 *
 * <p>Punt van aandacht bij het programmeren: Players <strong>moeten</strong> een unieke naam hebben: De naam wordt veel gebruikt voor identificatie.</p>
 *
 *
 * <h3 id="leaderboard">Leaderboard</h3>
 *
 * <p>Het leaderboard is een extra optie waar we het bij het bespreken van het protocol niet aan toe zijn gekomen. Ik heb daarom een eigen packet hiervoor geschreven. Hierin worden maximaal 50 entries verstuurd, met daarin naam, winst, verlies en spellen gespeeld.</p>
 *
 *
 * <h3 id="errorcodes">Errorcodes</h3>
 *
 * <p>Als er een error wordt verstuurd, wordt dit gedaan met een 'id', de header van de packet waardoor de fout is ontstaan. Aangezien numerieke ID's veel gedoe zijn, en lastig debuggen, heb ik gekozen voor deze makkelijkere optie. </p>
 *
 *
 * <h3 id="over-delimiters">Over Delimiters</h3>
 *
 * <p>Ik heb gekozen voor een dubbele carriage return (<code>\n\n</code>) als delimiter als footer omdat dit het debuggen iets makkelijker maakt: je kunt hiermee ook heel lange packets maken met enige layout erin, zoals in <code>BOARD</code>. Hierin zou je dan bijvoorbeeld elke rij een newline kunnen geven, zodat je het in de terminal ook als nieuwe lijnen ziet.</p>
 *
 * <p>Als delimiter tussen argumenten gebruiken wij een spatie (<code> <\code>) omdat dit makkelijk en handig is.</p>
 *
 * <p>Een losse carriage return mag overal in een packet voorkomen, behalve:
 *
 * <ul>
 *     <li>In een argument</li>
 *     <li>Achter een andere carriage return</li>
 * </ul></p>
 *
 *
 * <h2 id="packets">Packets</h2>
 *
 * <p>Hierop volgt een lijst met overeengekomen packets. Deze zijn gesorteerd op type en waar ze geimplementeerd moeten zijn. </p>
 *
 * <p>Per packet wordt ook het datatype erbijgegeven, dit om type conflicts tegen te werken. Ook is de maximale lengte van een <code>String</code>-object gegeven, om hier de verschillende conflicten tegen te gaan.</p>
 *
 * <p>Als laatste opmerking over de packets: Packets zijn op deze manier opgebouwd: eerst de waarde die hier bij het veld Name is ingevuld, daarna de waarden van Content. Als einde van een packet hebben we een delimiter, dit is een dubbele newline (<code>\n\n</code>). Voorbeeld:</p>
 *
 * <p><code>CONNECT Matthias CHAT CUSTOM_BOARD\n\n</code></p>
 *
 * <p>De opbouw van een packet is als volgt:</p>
 *
 * <p>&lt; nr &gt; &lt; Name &gt; <br>
 *     Name: &lt; header van packet &gt; <br>
 *     Descriptie: &lt; descriptie &gt; <br>
 *     Content: &lt; lijst van dingen die het packet bevat&gt; <br>
 *         * &lt; Name content&gt;: &lt; Content type&gt; - &lt; Verdere info over content &gt;</p>
 *
 * <p>Voorbeeld:</p>
 *
 * <ol>
 *     <li>Connect <br>
 *         Name: <code>CONNECT</code> <br>
 *         Descriptie: Packet dat verzonden wordt naar de server om een connectie te starten. <br>
 *         Content: <code>&lt;Player Name&gt;</code> <code>&lt;Features[]&gt;</code> <br>
 *         <ul>
 *             <li><code>Player Name</code>: <code>String</code> (31) - De naam van de speler die wil connecten.</li>
 *             <li><code>Features</code>: <code>Feature[]</code> - Een lijst van <code>Feature</code>s, met spaties van elkaar gescheiden. <br>
 *                 <code>Feature</code>: <code>String</code> (15) - Een unieke naam van een feature.
 *             </li>
 *     	   </ul>
 *     </li>
 * </ol>
 *
 *
 * <h2 id="constanten">Constanten</h2>
 *
 * <p>De settings die (nu) op een server kunnen zitten zijn:</p>
 *
 * <ul>
 *     <li><code>CUSTOM_BOARD</code> - Maak een bord aan met een andere grootte dan 7 * 6</li>
 *     <li><code>CHAT</code> - Chat client in je gameclient</li>
 *     <li><code>STATISTICS</code> - Player Statistics worden in je server bijgehouden.</li>
 * </ul>
 *
 *
 * <h2 id="tot-slot">Tot slot</h2>
 *
 * <p>Deze specificatie is gemaakt naar wat ik heb meegekregen van de vergadering op 7 januari, en naar eigen inzicht. Zit er een fout in, heb je een opmerking of wil je meer features? Stuur voor specifieke vragen een mail naar <code>m.j.vandemeent@student.utwente.nl</code></p>
 *
 * <p>Parameters omringd met blokhaken (<code>[]</code> zijn optioneel. Dit hoeft niet per se gebruikt te worden bij het communiceren, maar kunnen voor extra features gebruikt worden. Hoekhaken daarentegen (<code><></code>)zijn verplicht. </p>
 *
 */

public class Protocol {
	public static class Client {
		/**
		 * <h3 id="client">client</h3>
		 */

		/**
		 * <p>Connect <br>
		 *     Name: <code>CONNECT</code> <br>
		 *     Descriptie: Packet dat verzonden wordt om een connectie te starten. <br>
		 *     Content: <code>&lt;Player Name&gt;</code> <code>&lt;Features&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Player Name</code>: <code>String</code> (15) - De naam van de speler die wil connecten.</li>
		 *         <li><code>Features</code>: <code>Feature[]</code> - Een lijst van <code>Feature</code>s, met spaties van elkaar gescheiden. <br>
		 *             <code>Feature</code>: <code>String</code> (15) - Een unieke naam voor een feature.
		 *         </li>
		 *     </ul>
		 */

		public static final String CONNECT = "CONNECT";

		/**
		 * <p>Quit <br>
		 *     Name: <code>QUIT</code> <br>
		 *     Descriptie: Packet dat verzonden wordt om de verbinding te verbreken. <br>
		 *     Content: [<code>&lt;Reason&gt;</code>]</p>
		 *
		 *     <ul>
		 *         <li><code>Reason</code>: <code>String</code> (15) - De reden van het verbreken van de verbinding.</li>
		 *     </ul>
		 */

		public static final String QUIT = "QUIT";

		/**
		 * <p>Invite <br>
		 *     Name: <code>INVITE</code> <br>
		 *     Descriptie: Packet dat verzonden wordt om een spel te starten met de aangegeven tegenstander. <br>
		 *     Content: <code>&lt;Opponent Name&gt;</code>  [<code>&lt;BoardX&gt;</code> <code>&lt;BoardY&gt;</code> [<code>&lt;Settings&gt;</code>]]</p>
		 *
		 *     <ul>
		 *         <li><code>Opponent Name</code>: <code>String</code> (15) - De naam van de speler die de invite moet ontvangen.</li>
		 *         <li><code>BoardX</code>: <code>short</code> - De breedte van het spelbord. Standaardwaarde is 7. Minimaal 4.</li>
		 *         <li><code>BoardY</code>: <code>short</code> - De hoogte van het spelbord. Standaardwaarde is 6. Minimaal 4.</li>
		 *         <li><code>Settings</code>: Eigen inbreng - Verdere settings die je mee wilt geven in het spel. </li>
		 *     </ul>
		 */

		public static final String INVITE = "INVITE";

		/**
		 * <p>Accept Invite <br>
		 *     Name: <code>ACCEPT</code> <br>
		 *     Descriptie: Packet door de uitgedaagde partij wordt verzonden om op een invite in te gaan. <br>
		 *     Content: <code>&lt;Opponent Name&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Opponent Name</code>: <code>String</code> (15) - De naam van degene die de uitgedaagde partij heeft uitgedaagd.</li>
		 *     </ul>
		 */

		public static final String ACCEPT_INVITE = "ACCEPT";

		/**
		 * <p>Decline Invite <br>
		 *     Name: <code>DECLINE</code> <br>
		 *     Descriptie: Packet die door de uitgedaagde partij wordt verzonden om een invite af te slaan. <br>
		 *     Content: <code>&lt;Opponent Name&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Opponent Name</code>: <code>String</code> (15) - De naam van degene die de uitgedaagde partij heeft uitgedaagd.</li>
		 *     </ul>
		 */

		public static final String DECLINE_INVITE = "DECLINE";

		/**
		 * <p>Move <br>
		 *     Name: <code>MOVE</code> <br>
		 *     Descriptie: Bevat de kolom waarin de volgende steen in wordt gedaan. <br>
		 *     Content: <code>&lt;Column&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Column</code>: <code>short</code> - De kolom waarin de move wordt gezet.</li>
		 *     </ul>
		 */

		public static final String MOVE = "MOVE";

		/**
		 * <p>Chat <br>
		 *     Name: <code>CHAT</code> <br>
		 *     Descriptie: Bevat een chatmessage <br>
		 *     Content: <code>&lt;Chat&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Chat</code>: <code>String</code> (512) - De boodschap aan de server chat</li>
		 *     </ul>
		 */

		public static final String CHAT = "CHAT";

		/**
		 * <p>Request Board <br>
		 *     Name: <code>REQUEST</code> <br>
		 *     Descriptie: Vraagt het <code>Board</code> aan van de server <br>
		 *     Content: none</p>
		 */

		public static final String REQUEST_BOARD = "REQUEST";

		/**
		 * <p>Request Lobby <br>
		 *     Name: <code>LOBBY</code> <br>
		 *     Descriptie: Vraag de lijst met on-line spelers aan. <br>
		 *     Content: none</p>
		 */

		public static final String REQUEST_LOBBY = "LOBBY";

		/**
		 * <p>Request Leaderboard <br>
		 *     Name: <code>LEADERBOARD</code> <br>
		 *     Descriptie: Vraag het leaderboard aan <br>
		 *     Content: none</p>
		 */

		public static final String REQUEST_LEADERBOARD = "LEADERBOARD";

		/**
		 * <p>Error <br>
		 *     Name: <code>ERROR</code><br/>
		 *     Descriptie: Zend een error naar de server toe.<br/>
		 *     Content: <code>&lt;Error Code&gt;</code> <code>&lt;Message&gt;</code></p>
		 *     <ul>
		 *         <li><code>Error Code</code>: <code>String</code> - De code is de header van het bericht waar de fout door is ontstaan. </li>
		 *         <li><code>Message</code>: <code>String</code> (255) - Het bericht dat je aan je error hangt. Hierin kan je extra info tonen over wat er precies is foutgegaan.</li>
		 *     </ul>
		 */

		public static final String ERROR = "ERROR";

		/**
		 * <p>Ping <br>
		 *     Name: <code>PING</code><br/>
		 *     Descriptie: Vraag een respons van de server aan, om te kijken hoe snel deze reageert en om te kijken of de verbinding nog bestaat.<br/>
		 *     Content: none</p>
		 */

		public static final String PING = "PING";

	}

	public static class Server {
		/**
		 * <h3 id="server">Server</h3>
		 */

		/**
		 * <p>Accept Connect <br>
		 *     Name: <code>OK</code> <br>
		 *     Descriptie: Signaal dat de connectie is gemaakt en het aangeven van welke functies allemaal zijn toegestaan op deze server. <br>
		 *     Content: <code>&lt;Features&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Features</code>: <code>Feature</code> [] - De lijst met <code>Feature</code>s die wordt toegestaan op de server voor die client, gescheiden door spaties. <br>
		 *         	   <code>Feature</code>: <code>String</code> (15) - De unieken naam van een feature.
		 *         </li>
		 *     </ul>
		 */

		public static final String ACCEPT_CONNECT = "OK";

		/**
		 * <p>Error <br>
		 *     Name: <code>ERROR</code> <br>
		 *     Descriptie: Een errormessage <br>
		 *     Content: <code>&lt;Error Code&gt;</code> <code>&lt;Message&gt;</code></p>
		 *     <ul>
		 *         <li><code>Error Code</code>: <code>String</code> - De code is de header van het bericht waar de fout door is ontstaan. </li>
		 *         <li><code>Message</code>: <code>String</code> (255) - Het bericht dat je aan je error hangt. Hierin kan je extra info tonen over wat er precies is foutgegaan.</li>
		 *     </ul>
		 */

		public static final String ERROR = "ERROR";

		/**
		 * <p>Lobby <br>
		 *     Name: <code>LOBBY</code> <br>
		 *     Descriptie: Een lijst met mensen die zich op het moment in de lobby bevinden. Wordt door de server verstuurd bij Connect/Disconnect van een speler, en wanneer aangevraagd. <br>
		 *     Content: <code>&lt;Players&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Players</code>: <code>Player[]</code> - Een lijst met players <br>
		 *             <code>Player</code>: <code>String</code> (15) - De naam van de player
		 *         </li>
		 *     </ul>

		*/

		public static final String LOBBY = "LOBBY";

		/**
		 * <p>Invite <br>
		 *     Name: <code>INVITE</code> <br>
		 *     Descriptie: Een packet die naar de uitgedaagde speler wordt gestuurd. <br>
		 *     Content: <code>&lt;Opponent Name&gt;</code> [<code>&lt;BoardX&gt;</code> <code>&lt;BoardY&gt;</code> [<code>&lt;Settings&gt;</code>]]</p>
		 *
		 *     <ul>
		 *         <li><code>Opponent Name</code>: <code>String</code> (15) - De naam van de tegenstander</li>
		 *         <li><code>BoardX</code>: <code>short</code> | <code>int</code> - De breedte van het bord. Standaard 7, kleinste waarde 4.</li>
		 *         <li><code>BoardY</code>: <code>short</code> | <code>int</code> - De hoogte van het bord. Standaard 6, kleinste waarde 4.</li>
		 *         <li><code>Settings</code>: Eigen type - Zelf in te vullen ruimte, dit kan gebruikt worden voor extra settings.</li>
		 *     </ul>
		 */

		public static final String INVITE = "INVITE";

		/**
		 * <p>Decline invite<br>
		 *     Name: <code>DECLINE</code> <br>
		 *     Descriptie: De packet die naar de uitdager wordt teruggestuurt om te zeggen dat zijn uitdaging is afgewezen.. <br>
		 *     Content: <code>&lt;Opponent Name&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Opponent Name</code>: <code>String</code> (15) - De naam van de uitdagende partij.</li>
		 *     </ul>
		 */

		public static final String DECLINE_INVITE = "DECLINE";

		/**
		 * <p>Game Start <br>
		 *     Name: <code>START</code> <br>
		 *     Descriptie: Een packet dat naar de spelers wordt gestuurd om te laten weten dat het spel gestart is. <br>
		 *     Content: <code>&lt;Player 1&gt;</code> <code>&lt;Player 2&gt;</code> [<code>&lt;Extras&gt;</code>]</p>
		 *
		 *     <ul>
		 *         <li><code>Player 1</code>: <code>String</code> (15) - Naam van de eerste speler</li>
		 *         <li><code>Player 2</code>: <code>String</code> (15) - Naam van de tweede speler</li>
		 *         <li><code>Extras</code>: Eigen type - Zelf in te vullen ruimte, die gebruikt kan worden voor bijvoorbeeld extra spelers of meekijkers</li>
		 *     </ul>
		 */

		public static final String GAME_START = "START";

		/**
		 * <p>Game End <br>
		 *     Name: <code>END</code> <br>
		 *     Descriptie: Een packet dat naar de spelers wordt gestuurd om te laten weten dat het spel is gestopt <br>
		 *     Content: <code>&lt;Type&gt;</code> [<code>&lt;Winner Name&gt;</code>]</p>
		 *
		 *     <ul>
		 *         <li><code>Type</code>: <code>String</code> &gt; <code>'WIN'</code> <code>'DISCONNECT'</code> <code>'DRAW'</code> - Type van einde spel</li>
		 *         <li><code>Winner Name</code>: <code>String</code> (15) - Naam van de winnaar, of andere info over de reden van het einde.</li>
		 *     </ul>
		 */

		public static final String GAME_END = "END";

		/**
		 * <p>Request Move <br>
		 *     Name: <code>REQUEST</code> <br>
		 *     Descriptie: Een packet dat verstuurd wordt naar de speler om aan te geven dat deze persoon aan de beurt is om een zet te doen. <br>
		 *     Content: none</p>
		 */

		public static final String REQUEST_MOVE = "REQUEST";

		/**
		 * <p>Move OK <br>
		 *     Name: <code>MOVE</code> <br>
		 *     Descriptie: Een packet dat naar de spelers gestuurd wordt om een move te laten doorgaan. <br>
		 *     Content: <code>&lt;Player Number&gt;</code> <code>&lt;Column&gt;</code> [<code>&lt;Player Name&gt;</code>]</p>
		 *
		 *     <ul>
		 *         <li><code>Player Number</code>: <code>byte</code> | <code>short</code> | <code>int</code> - Het startnummer van de speler die de zet heeft gedaan.</li>
		 *         <li><code>Column</code>: <code>short</code> - De kolom waar de zet in gedaan wordt.</li>
		 *         <li><code>Player Name</code>: <code>String</code> (15) - De naam van de speler die net een zet heeft gedaan.</li>
		 *     </ul>
		 */

		public static final String MOVE_OK = "MOVE";

		/**
		 * <p>Board <br>
		 *     Name: <code>BOARD</code> <br>
		 *     Descriptie: Een packet waarin het huidige bord verstuurd wordt. <br>
		 *     Content: <code>&lt;BoardX&gt;</code> <code>&lt;BoardY&gt;</code> <code>&lt;Board&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>BoardX</code>: <code>short</code> - De breedte van het bord</li>
		 *         <li><code>BoardY</code>: <code>short</code> - De hoogte van het bord</li>
		 *         <li><code>Board</code>: <code>byte[]</code> - Een array van (breedte * hoogte) getallen lang, waarin de nummers van de spelers staan. Start links onderin het bord, het wordt per rij weggeschreven, van links naar rechts in de rij, beginnend bij de onderste rij, naar boven..</li>
		 *     </ul>
		 */

		public static final String BOARD = "BOARD";

		/**
		 * <p>Chat <br>
		 *     Name: <code>CHAT</code> <br>
		 *     Descriptie: Een packet wat een chatbericht bevat <br>
		 *     Content: <code>&lt;Player Name&gt;</code> <code>&lt;Chat&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Player Name</code>: <code>String</code></li>
		 *         <li><code>Chat</code>: <code>String</code> (512)</li>
		 *     </ul>
		 */

		public static final String CHAT = "CHAT";

		/**
		 * <p>Leaderboard <br>
		 *     Name: <code>LEADERBOARD</code> <br>
		 *     Descriptie: Een packet waarin de statistieken van een aantal spelers worden verstuurd. <br>
		 *     Content: <code>&lt;Player Statistics&gt;</code></p>
		 *
		 *     <ul>
		 *         <li><code>Player Statistics</code>: <code>Player Statistic</code> (50) - De statistieken van maximaal 50 spelers tegelijk worden verstuurd. <br>
		 *             <code>Player Statistic</code>: <code>&lt;Player Name&gt;</code> <code>&lt;Games Won&gt;</code> <code>&lt;Games Lost&gt;</code> <code>&lt;Games Played&gt;</code> <code>&lt;Ranking&gt;</code> <br>
		 *             <ul>
		 *                 <li><code>Player Name</code>: <code>String</code> (15) - Naam van de speler in de betreffende statistiek</li>
		 *                 <li><code>Games Won</code>: <code>int</code> - Aantal games gewonnen</li>
		 *                 <li><code>Games Lost</code>: <code>int</code> - Aantal games verloren</li>
		 *                 <li><code>Games Played</code>: <code>int</code> - Aantal games gespeeld</li>
		 *                 <li><code>Ranking</code>: <code>int</code> - Ranking op de server</li>
		 *             </ul>
		 *         </li>
		 *     </ul>
		 */

		public static final String LEADERBOARD = "LEADERBOARD";

		/**
		 * <p>Pong <br>
		 *     Name: <code>PONG</code><br/>
		 *     Descriptie: De respons van de server op een <code>PING</code>-packet.<br/>
		 *     Content: none</p>
		 */

		public static final String PONG = "PONG";
	}

	public static class Features {

		/**
		 * <p>De verschillende features die geimplementeerd kunnen worden.</p>
		 *
		 * <p>Let op! Het protocol voor <code>SECURITY</code> en <code>MULTIPLAYER</code> is (nog) niet vastgelegd.</p>
		 */

		public static final String CHAT = "CHAT";
		public static final String LEADERBOARD = "LEADERBOARD";
		public static final String CUSTOM_BOARD_SIZE = "CUSTOM_BOARD";

		public static final String SECURITY = "SECURITY";
		public static final String MULTIPLAYER = "MULTIPLAYER"; // Deze functie wordt niet door het protocol gespecificeerd.
	}

	public static class Settings {

		/**
		 * <p>De verschillende settings van het protocol.</p>
		 */

		/**
		 * <p>Het protocol heeft characterencoding UTF-16. Dit is de standaard encoding van een string in java, dus daar zouden geen problemen mee moeten zijn.</p>
		 */

		public static final String ENCODING = "UTF-16";

		/**
		 * <p>Het aantal seconden voordat een client timeout. Dit is in de opdracht vastgesteld, en zal dus niet veranderen.</p>
		 */

		public static final int TIMEOUTSECONDS = 15;

		/**
		 * <p>Default server port nummer. <br>
		 *     <b>BELANGRIJK:</b> In de opdracht staat dat je bij het opstarten van de server een poortnummer moet invoeren. De waarde hier is dus niet een waarde die altijd opgaat. </p>
		 */

		public static final short DEFAULT_PORT = 2707;

		/**
		 * <p>Default delimiter tussen header en content, en tussen twee waarden in de content</p>
		 */

		public static final char DELIMITER = ' ';

		/**
		 * <p>Teken dat aan het einde van elke packet moet zitten, en dus niet in de rest van de waarden mag zitten.</p>
		 */

		public static final char PACKET_END = '\n';
	}
}