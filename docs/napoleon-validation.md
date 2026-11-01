# Campagne longue et combats 3D — 1er novembre 2026

## Aventure livrée

**Bonaparte · Les Cartes du Nil** : fiction historique en Égypte, en juillet 1798.
Camille Laurent et la cartographe Salma recherchent des relevés volés des routes de
l'eau, d'Alexandrie au Nil, au Caire et à Gizeh. Bonaparte, Amina, Youssef, Farid,
Desaix et Monge interviennent dans l'enquête.

- 117 scènes accessibles, quatre chapitres, deux fins.
- Les deux fins demandent au minimum 64 choix depuis le départ, vérifiés par
  parcours en largeur du graphe. Les détours permettent des visites répétées.
- Le premier choix de chaque scène principale forme une route sans combat.
  Un test sur le serveur a atteint la fin 64 après 64 choix, avec 11/11 HP.
- Les combats sont des choix explicites. Les jets de discrétion ratés mènent à
  une autre piste. Marcher, regarder et attendre ne consomment aucun tour logique.
- Les lieux restent des scènes procédurales du graphe. Il ne s'agit pas d'un
  territoire géographique continu ni de contenu nouveau généré à l'infini.

Le contexte s'appuie sur la [chronologie de la Fondation Napoléon](https://www.napoleon.org/histoire-des-2-empires/chronologies/chronologie-de-la-correspondance-generale-de-napoleon-bonaparte-tome-2-la-campagne-degypte-et-lavenement-1798-1799)
et la présentation de la [Description de l'Égypte par l'Assemblée nationale](https://www.assemblee-nationale.fr/dyn/histoire-et-patrimoine/revolution-francaise/volumes-illustres-la-description-de-l-egypte).
L'enquête et ses dialogues sont inventés.

## Référence demandée : médiane de 10 tours

Le profil **exploration-10-v1** utilise :

    S_ref(t) = q^(t²), avec q = 99309 / 100000.
    S_ref(9) > 1/2 et S_ref(10) ≤ 1/2.

Ces deux inégalités sont prouvées dans `explorationPolicy_median`. Un tour est
un choix de scène, avec son combat entier éventuel. Les actions du joueur de test
sont uniformes : choix de scène uniforme, puis manœuvre uniforme parmi les trois
manœuvres, puis cible vivante uniforme si la manœuvre attaque.

Les transitions aléatoires et les dégâts restent ceux du moteur Lean. La politique
uniforme appartient aux tests. Le joueur humain choisit librement.

L'admission compare les intervalles binomiaux conservateurs à 90 % aux bandes
existantes de largeur ±0,2 : décès au premier tour, puis décès exactement au tour
t+2 conditionnellement à la survie au tour t. Elle ne contraint pas directement
la médiane empirique à être exactement 10, ni toute la fonction de survie à
coïncider avec la référence. Les bornes de risque du test restent conditionnelles
au modèle d'échantillonnage binomial ; le générateur pseudo-aléatoire n'est pas
prouvé indépendant et uniforme.

Les anciennes aventures gardent leur profil legacy à six tours. Les nouveaux
Wishes sont soumis à 15 tours. Une sauvegarde conserve sa version de politique.

## Résultats statistiques

Le réglage du contenu utilise la graine **20261102**. Le contenu mécanique est
ensuite figé ; la validation utilise **20261103**, sans recherche d'une graine
favorable. Chaque fenêtre utilise 1 000 trajectoires et la limite existante de
200 rounds par combat. Aucune trajectoire n'a provoqué d'abandon du lot.

| Fenêtre | Décès cumulés dans la fenêtre | Observations dans la dernière ligne conditionnelle | Admission de toutes les lignes |
| --- | ---: | ---: | --- |
| 15 tours | 688 / 1 000 | 389 | Oui |
| 30 tours | 831 / 1 000 | 175 | Non : 4 lignes échouent |
| 60 tours | 934 / 1 000 | 68 | Non : 34 lignes échouent |

Dans le lot d'admission à 15 tours : **474 / 1 000 décès au plus tard au tour 10**,
soit **47,4 %**, avec un intervalle conservateur à 90 % de **44,53 % à 50,39 %**.
La médiane observée est **11 choix**. Le lot de réglage donnait 48,9 % au tour 10.

Les échecs tardifs correspondent à une mortalité plus faible que la référence :
les intervalles descendent sous la borne minimale autorisée. Plusieurs intervalles
recoupent encore la bande, ce qui reste insuffisant pour l'admission par inclusion.
Il y a moins d'observations tardives, mais aucune ligne n'a été masquée. **La
fairness n'est pas validée jusqu'à 30 ou 60 tours.** Ces diagnostics ne remplacent
pas le test d'admission fixé à 15 tours.

Changer la fenêtre change la consommation du flux pseudo-aléatoire de chaque
trajectoire. Les trois lots issus de la même graine ne sont donc pas les mêmes
1 000 trajectoires tronquées, ni trois réplications indépendantes. Les intervalles
sont des intervalles par ligne, pas une région de confiance simultanée à 90 %.

Données complètes : [15 tours](reports/napoleon-15-turns.json),
[30 tours](reports/napoleon-30-turns.json), [60 tours](reports/napoleon-60-turns.json).

## Temps mesurés sur cette machine

La campagne a été écrite localement pendant cette intervention. Aucune clé
ANTHROPIC_API_KEY n'était disponible. **Le temps d'une génération narrative par
l'API Claude n'a donc pas été mesuré.** Les nombres suivants commencent avec les
textes déjà écrits dans le script et excluent le travail de conception et de code.

| Étape | Mesure |
| --- | ---: |
| Assemblage du JSON à partir des textes écrits | 1,71 ms |
| Vérification de légalité des 117 scènes | 673 ms |
| Simulation, admission et rapport à 15 tours | 6 418 ms |
| Assemblage + lancement du vérificateur + installation, temps réel total | 9,51 s |
| Construction du premier décor dans le navigateur | 6,50 ms |
| Première image rendue, depuis le début de cette construction | 79,10 ms |
| Exemple de combat : réponse du moteur | 11,2 ms |
| Même combat, réponse et animations à vitesse ×2 | 1 808,8 ms |

Le premier décor a été mesuré dans le navigateur intégré, en 1280 × 720. Ces
mesures ponctuelles ne sont ni des moyennes ni des garanties sur un autre appareil.
La mesure de première image exclut le réseau et la revalidation de la sauvegarde.
Le chargement d'une sauvegarde refait l'admission ; il peut donc prendre plusieurs
secondes. Les peintures SVG optionnelles ne sont pas nécessaires au décor 3D.

Les futurs appels Wish exposent `generation.timings` dans la vue JSON : temps API
cumulé, validation cumulée et total jusqu'à la sauvegarde, avec indication du mode
réel ou enregistré. Le navigateur expose `data-build-ms` et `data-first-frame-ms`
sur la vue 3D, ainsi que les temps de réponse/résolution sur le corps du document.

[Mesures enregistrées](reports/napoleon-timings.json).

## Combats et performance

Les dés visibles reprennent les faces des rapports Lean. Aucun dé de substitution
n'est tiré dans le navigateur. Les HP sont présentés au rythme des rapports de
dégâts ; l'état final du serveur n'est plus dévoilé avant leur lecture.

Les boutons et touches numériques sélectionnent les mêmes manœuvres et cibles
autorisées que les armes et boucliers dans la scène. Les rapports sans contenu
visuel n'ajoutent pas de pause. Les vitesses ×1, ×2 et instantanée modifient
uniquement la présentation. Les ombres statiques ne sont plus recalculées à
chaque image.

Le parcours du graphe du vérificateur déduplique désormais les nouvelles scènes
à chaque étape. Les chemins convergents ne multiplient plus les mêmes nœuds.
La propriété de validité des nœuds atteints et le théorème `check_sound` sont
conservés ; un test de régression couvre les chemins convergents.

## Vérifications et reproduction

    make napoleon
    make run PORT=8093
    make test-spatial
    lake build inspect-adventure
    .lake/build/bin/inspect-adventure campaigns/napoleon.json --horizon 14 --seed 20261103
    .lake/build/bin/inspect-adventure campaigns/napoleon.json --horizon 29 --seed 20261103
    .lake/build/bin/inspect-adventure campaigns/napoleon.json --horizon 59 --seed 20261103

Les deux dernières commandes renvoient le code 1 : c'est le résultat attendu des
diagnostics non admis, pas une erreur à contourner.

- Compilation Lean complète réussie ; nouveaux tests de persistance du profil,
  refus des versions inconnues et fenêtres legacy/nouvelle.
- 14 tests JavaScript réussis : correspondance des commandes, navigation,
  conservation des entrées et synchronisation des rapports.
- Vérification des règles et des images réussie.
- Audit des axiomes des théorèmes concernés : seulement propext,
  Classical.choice et Quot.sound. Aucun sorry ni nouvel axiome.
- Dans le navigateur : déplacement jusqu'à Napoléon et Salma, sélection spatiale
  d'un combat, attaque par bouton, raccourci numérique, dés, dégâts et mort.
  Mode instantané vérifié également : 16,6 ms de résolution, dont 7,2 ms de réponse
  serveur, sur un tour distinct. Aucune erreur de console pendant ce parcours.
- [Parcours de 64 choix](reports/napoleon-safe-path.json) par l'API réelle du serveur.
- Circuit Wish testé sur un serveur isolé avec les réponses enregistrées : premier
  brouillon refusé, correction admise, timings identifiés comme recorded-fixture
  (6 393 ms au total). Ce test ne mesure pas une génération par l'API Claude.

Le lancement de Chromium autonome par Playwright est bloqué par le bac à sable
macOS de cette session. Les vérifications visuelles utilisent le navigateur
intégré. `lake check` et Comparator exigent leur bac à sable Linux : ils restent
à exécuter sous Linux. La compilation et l'audit ne remplacent pas ce dernier
contrôle. La 3D demeure une interface testée, sans preuve formelle du rendu.
